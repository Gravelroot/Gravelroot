#
# Copyright (c) 2020 Vitalis Salis.
#
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
#
from .base import BaseFormatter


class Simple(BaseFormatter):
    def __init__(self, cg_generator):
        self.cg_generator = cg_generator
        self.print_stmts = {}
        self.all_paths = []
        self.hierarchy_graph = self.cg_generator.output_hierarchy_graph()

    # def generate(self):
    #     output = self.cg_generator.output()
    #     output_cg = {}
    #     for node in output:
    #         output_cg[node] = list(output[node])
    #     return output_cg

    def generate(self):
        output_re = self.cg_generator.output_re()
        output_cg = {}
        sinks = self.cg_generator.sink_manager.get_sink_points()
        middles = self.cg_generator.output_middles()
        for sink in sinks:
            if sink not in output_re:
                continue
            self.find_all_paths(sink, [], output_re, [], dict())
        for index, path in enumerate(self.all_paths):
            path_key = f'Path{index + 1}'
            path_str = ' -> '.join(reversed(path))
            print(path_key)
            print(path_str)
            output_cg[path_key] = {'condition': [], 'path': path_str, 'middles': [], 'taints': []}
            self.print_condition(path[1], output_cg[path_key]['condition'], output_re)
            self.print_stmt(path[-1], path, output_cg[path_key], middles, [])

        return output_cg

    def find_all_paths(self, current_node, current_path, data, find_conflict, met_cls_dict):
        if current_node in current_path:
            self.all_paths.append(current_path.copy())
            return

        if 'HypotheticalDocumentEmbedder.embed_query' in current_node:
            return

        flag = False
        sig_met = None
        if '.' in current_node:
            sig_cls, sig_met = current_node.rsplit('.', 1)
            if sig_met not in met_cls_dict:
                met_cls_dict[sig_met] = sig_cls
            elif (self.hierarchy_graph.have_common_parent(met_cls_dict[sig_met], sig_cls)
                  and not (self.hierarchy_graph.is_subclass(met_cls_dict[sig_met], sig_cls)
                           or self.hierarchy_graph.is_subclass(sig_cls, met_cls_dict[sig_met]))):
                return
        else:
            sig_cls = current_node.rsplit('.', 1)[0]
        if not self.hierarchy_graph.has_class(sig_cls) and '.' in sig_cls:
            candidate = sig_cls.rsplit('.', 1)[0]
            if self.hierarchy_graph.has_class(candidate):
                sig_cls = candidate

        if len(find_conflict) >= 2:
            second_last = find_conflict[-2]
            last = find_conflict[-1]
            if sig_cls != last:
                if (
                        not self.hierarchy_graph.get_exist_edge(current_node, current_path[-1])
                        and (self.has_conflicts(sig_cls, last, second_last)
                             or self.iter_has_conflicts(current_node, last, second_last))
                        and not (second_last == sig_cls and last in data and current_node in data[last])
                ):
                    print('have conflict: ' + sig_cls + '   ' + second_last)
                    return
                find_conflict.append(sig_cls)
            else:
                flag = True
        else:
            find_conflict.append(sig_cls)

        current_path.append(current_node)

        if not data[current_node]:
            self.all_paths.append(current_path.copy())
        else:
            for next_node in data[current_node]:
                self.find_all_paths(next_node, current_path, data, find_conflict, met_cls_dict)

        if not flag:
            find_conflict.pop()
        if sig_met:
            met_cls_dict.pop(sig_met, None)
        current_path.pop()

    def has_conflicts(self, sig_cls, last, second_last):
        return self.hierarchy_graph.is_subclass(second_last, last) and self.hierarchy_graph.is_subclass(sig_cls, last)

    def iter_has_conflicts(self, sig_meth, last, second_last):
        must_cls_list = self.hierarchy_graph.get_exist_cls_edge(sig_meth)
        if second_last in must_cls_list:
            return False
        for must_cls in must_cls_list:
            if self.hierarchy_graph.is_subclass(second_last, last) and self.hierarchy_graph.is_subclass(must_cls, last) and must_cls != last:
                return True

    def print_stmt(self, node, path, output_cg, middles, find_loop, indent=0, need_subt=False):
        taint_path = output_cg['taints']
        if node in find_loop:
            return
        find_loop.append(node)
        if ':' in node:
            pnode = node.split(':')[1]
        else:
            pnode = node
        edges_with_name = self.cg_generator.cg.get_edges_with_name(pnode)
        taint_with_name = self.cg_generator.cg.get_taints_with_name(pnode)
        if not taint_with_name:
            indent_str = '   ' * indent
            taint_path.append(indent_str + 'method: ' + node)
            print(indent_str + 'method: ' + node)
            if node not in path:
                return
            index = path.index(node)
            if index > 0:
                node = path[index - 1]
                edges_with_name = self.cg_generator.cg.get_edges_with_name(node)
                taint_with_name = self.cg_generator.cg.get_taints_with_name(node)
            else:
                return

        call_next_sink = False
        next_sink_node = None
        if node in path:
            index = path.index(node)
            if index > 0:
                next_sink_node = path[index - 1]
        if need_subt:
            indent -= 1
        indent_str = '   ' * indent

        for line, stmt in taint_with_name.items():
            taint_path.append(indent_str + 'method: ' + node)
            taint_path.append(indent_str + '----->' + stmt + '  ' + line)
            print(indent_str + 'method: ' + node)
            print(indent_str + '----->' + stmt + '  ' + line)
            is_middle = False
            if intersection := self.cg_generator.output_intersections().get(node):
                for call_mid_method in intersection['line_num'].get(int(line.replace('line: ', '')), []):
                    if call_mid_method in path:
                        continue
                    mod_name, method = call_mid_method.split(':')
                    potent_mid_method = middles[mod_name]['potent_method']
                    middle_callee = potent_mid_method[method]['callee']
                    result_callee = self.determine_skip_middle(path, node, middle_callee)
                    self.iter_middle(path, result_callee, middles, [call_mid_method], output_cg, indent)
                    is_middle = True
                if is_middle:
                    continue
            elif stmt and next_sink_node and next_sink_node not in stmt and '@' in stmt:
                taint_method = stmt.split('@')[1]
                for _line, _stmt in (self.cg_generator.cg.get_taints_with_name(taint_method) or {}).items():
                    if '@' in _stmt:
                        next_taint_method = _stmt.split('@')[1]
                        find_loop.append(next_taint_method)
                        self.print_stmt(taint_method, find_loop, output_cg, middles, find_loop, indent + 1)
            if line in edges_with_name:
                for sub_index, call_next_method in enumerate(edges_with_name[line]):
                    if len(edges_with_name[line]) > 1:
                        inter = set(edges_with_name[line]) & set(path)
                        if inter and call_next_method not in inter:
                            continue
                    if next_sink_node and next_sink_node == call_next_method:
                        call_next_sink = True
                    self.print_stmt(call_next_method, path, output_cg, middles, find_loop, indent + 1, call_next_sink)

        if next_sink_node and not call_next_sink:
            self.print_stmt(next_sink_node, path, output_cg, middles, find_loop)

    def determine_skip_middle(self, path, call_next_method, middle_callee):
        result = set()
        if call_next_method not in path:
            return middle_callee
        index = path.index(call_next_method)

        if index < len(path):
            next_path_class = path[index - 1].rsplit('.', 1)[0]
            for middle_method in middle_callee:
                mod_name, met_name = middle_method.split(':')
                cls_name = met_name.rsplit('.', 1)[0]
                if (
                        self.hierarchy_graph.have_common_parent(next_path_class, mod_name + '.' + cls_name)
                        and not self.hierarchy_graph.is_subclass(mod_name + '.' + cls_name, next_path_class)
                ):
                    continue
                result.add(middle_method)
        return result

    def iter_middle(self, call_path, caller_message, middles, path, output_cg, indent=0):
        indent_str = '   ' * indent
        for caller in caller_message:
            if caller in path:
                continue
            mod_name, met_name = caller.split(':')
            path.append(caller)
            if mod_name == 'openai':
                print(indent_str + 10*'===============')
                print(indent_str + 'path of call openai: ' + ' -> '.join(path))
                print(indent_str + 10*'===============')
                output_cg['middles'].append(' -> '.join(path))
                return
            middle_callee = middles[mod_name]['potent_method'][met_name]['callee']
            self.iter_middle(call_path, middle_callee, middles, path, output_cg, indent)
            if 'openai:create' in path:
                return
            path.pop()

    def print_condition(self, node, condition_path, cg, path=None, print_count=[0], max_print=5):
        if path is None:
            have_condition = False
            node, _, _ = node.rpartition('.')
            node += ".__init__"
            for _ in range(3):
                if node in cg:
                    have_condition = True
                    break
                node, _, _ = node.rpartition('.')
            if not have_condition:
                return
            path = []

        if node in path:
            return

        path.append(node)

        if node not in cg or not cg[node]:
            if len(path) > 0:
                if print_count[0] < max_print:
                    print('condition: ')
                    condi_path = ' -> '.join(reversed(path))
                    print(condi_path)
                    print_count[0] += 1
                condition_path.append(' -> '.join(reversed(path)))
                path.pop()
            return

        for condition in cg[node]:
            condition_class = condition.rsplit('.', 1)[0]
            node_class = node.rsplit('.', 1)[0]
            if self.hierarchy_graph.is_subclass(node_class, condition_class):
                condition = node_class
            self.print_condition(condition, condition_path, cg, path, print_count, max_print)

        path.pop()
