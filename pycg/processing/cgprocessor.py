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
import ast
import os

from pycg import utils
from pycg.machinery.definitions import Definition
from pycg.machinery.contexts import ContextManager
from pycg.processing.base import ProcessingBase


class CallGraphProcessor(ProcessingBase):
    def __init__(
            self,
            filename,
            modname,
            import_manager,
            scope_manager,
            def_manager,
            class_manager,
            module_manager,
            sink_manager,
            intersection_manager,
            middle_manager,
            context_manager,
            call_graph=None,
            modules_analyzed=None,
    ):
        super().__init__(filename, modname, modules_analyzed)
        # parent directory of file
        self.parent_dir = os.path.dirname(filename)

        self.import_manager = import_manager
        self.scope_manager = scope_manager
        self.def_manager = def_manager
        self.class_manager = class_manager
        self.module_manager = module_manager
        self.sink_manager = sink_manager
        self.intersection_manager = intersection_manager
        self.middle_manager = middle_manager
        self.call_graph = call_graph
        self.call_graph.set_hierarchy_graph(self.sink_manager.get_hierarchy_graph())
        self.call_graph.set_intersections(self.intersection_manager.get_nodes())
        self.call_graph.set_middles(self.middle_manager.get_nodes())
        self.context_manager = context_manager

        self.closured = self.def_manager.transitive_closure()
        self.taints = self.def_manager.transitive_taints()
        self.hierarchy_graph = self.sink_manager.get_hierarchy_graph()
        self.resource_field = None

    def visit_Module(self, node):
        self.call_graph.add_node(self.modname, self.modname)
        super().visit_Module(node)

    def visit_For(self, node):
        self.visit(node.iter)
        self.visit(node.target)
        # assign target.id to the return value of __next__ of node.iter.it
        # we need to have a visit for on the postprocessor also
        iter_decoded = self.decode_node(node.iter)
        for item in iter_decoded:
            if not isinstance(item, Definition):
                continue
            names = self.closured.get(item.get_ns(), [])
            for name in names:
                iter_ns = utils.join_ns(name, utils.constants.ITER_METHOD)
                next_ns = utils.join_ns(name, utils.constants.NEXT_METHOD)
                if self.def_manager.get(iter_ns):
                    self.local_call(node, iter_ns)
                    self.call_graph.add_edge(self.current_method, iter_ns)
                if self.def_manager.get(next_ns):
                    self.local_call(node, next_ns)
                    self.call_graph.add_edge(self.current_method, next_ns)

        super().visit_For(node)

    def visit_Lambda(self, node):
        counter = self.scope_manager.get_scope(self.current_ns).inc_lambda_counter()
        lambda_name = utils.get_lambda_name(counter)
        lambda_fullns = utils.join_ns(self.current_ns, lambda_name)

        self.call_graph.add_node(lambda_fullns, self.modname)

        super().visit_Lambda(node, lambda_name)

    def visit_Raise(self, node):
        if not node.exc:
            return
        self.visit(node.exc)
        decoded = self.decode_node(node.exc)
        for d in decoded:
            if not isinstance(d, Definition):
                continue
            names = self.closured.get(d.get_ns(), [])
            for name in names:
                pointer_def = self.def_manager.get(name)
                if pointer_def.get_type() == utils.constants.CLS_DEF:
                    init_ns = self.find_cls_fun_ns(name, utils.constants.CLS_INIT)
                    for ns in init_ns:
                        self.local_call(node, ns)
                        self.call_graph.add_edge(self.current_method, ns)
                if pointer_def.get_type() == utils.constants.EXT_DEF:
                    self.local_call(node, name)
                    self.call_graph.add_edge(self.current_method, name)

    def visit_ClassDef(self, node):
        self.resource_field = dict()
        super().visit_ClassDef(node)

    def visit_AsyncFunctionDef(self, node):
        self.visit_FunctionDef(node)

    def visit_FunctionDef(self, node):
        name_stack = self.name_stack[:]
        class_name = ".".join(name_stack[1:])
        fun_name = f"{class_name}.{node.name}" if class_name else node.name
        target_sinks = self.sink_manager.get_node(self.modname)
        if "__init__" not in fun_name and (not target_sinks or fun_name not in target_sinks["sink_method_user"]):
            return

        for decorator in node.decorator_list:
            self.visit(decorator)
            decoded = self.decode_node(decorator)
            for d in decoded:
                if not isinstance(d, Definition):
                    continue
                names = self.closured.get(d.get_ns(), [])
                for name in names:
                    self.local_call(node, name)
                    self.call_graph.add_edge(self.current_method, name)

        for arg in node.args.args:
            annotated_id = None
            if isinstance(arg.annotation, ast.Subscript) and isinstance(arg.annotation.slice, ast.Name):
                annotated_id = arg.annotation.slice.id
            elif isinstance(arg.annotation, ast.Name):
                annotated_id = arg.annotation.id
            if self.resource_field is not None and annotated_id in self.sink_manager.get_potent_method_nodes():
                if node.name == '__init__':
                    self.resource_field[class_name + '.' + arg.arg] = annotated_id
                else:
                    self.resource_field[self.current_method + '.' + node.name + '.' + arg.arg] = annotated_id

        self.call_graph.add_node(
            utils.join_ns(self.current_ns, node.name), self.modname
        )
        super().visit_FunctionDef(node)

    def visit_Assign(self, node):
        if isinstance(node.value, ast.Constant):
            return
        self.visit(node.value)
        for target in node.targets:
            self.is_taint(target, node)

    def visit_Call(self, node):
        def create_ext_edge(name, ext_modname):
            self.add_ext_mod_node(name)
            self.call_graph.add_node(name, ext_modname)
            if name == 'isinstance':
                return
            self.local_call(node, name)
            self.call_graph.add_edge(self.current_method, name)

        # First visit the child function so that on the case of
        #       func()()()
        # we first visit the call to func and then the other calls
        func_name = getattr(node.func, "id", None) or getattr(node.func, "attr", None)

        if func_name in {'isinstance', 'print', 'error', 'lower', 'super'}:
            return

        for arg in node.args:
            self.is_taint(arg, node)
            self.visit(arg)
            if func_name == 'eval' and isinstance(arg, ast.Constant):
                for stmt in ast.parse(arg.value).body:
                    self.generic_visit(stmt)

        for keyword in node.keywords:
            self.is_taint(keyword, node)
            self.visit(keyword.value)

        self.visit(node.func)

        sig_caller_cls = '.'.join([self.modname] + self.class_stack)
        class_name = getattr(node.func.value, 'id', None) if hasattr(node.func, 'value') else None
        param_field = False
        nfv = getattr(node.func, 'value', None)
        if isinstance(nfv, ast.Call) and isinstance(nfv.func, ast.Name):
            class_name = nfv.func.id
        elif isinstance(nfv, ast.Attribute) and getattr(nfv.value, 'id', None) == 'self':
            current_class = '.'.join(self.class_stack)
            sign_field = f"{current_class}.{nfv.attr}"
            if self.resource_field and sign_field in self.resource_field:
                param_field = True
        elif self.resource_field and class_name and self.current_method + '.' + class_name in self.resource_field:
            param_field = True
        field_anno_cls_set = set()
        field_anno_cls = None
        receiver_is_cls = False
        if isinstance(node.func, ast.Attribute):
            sink_node = self.sink_manager.get_node(self.modname)
            re_decode = self.decode_node(node.func.value)
            for re in re_decode:
                if not isinstance(re, Definition):
                    continue
                if re.get_type() == utils.constants.CLS_DEF:
                    receiver_is_cls = True
                    re_cls = re.get_ns()
                    field_anno_cls_set.add(re.get_ns())
                    if not field_anno_cls or self.hierarchy_graph.is_subclass(field_anno_cls, re_cls):
                        field_anno_cls = re_cls
                elif sink_node and re.get_ns() in sink_node['sink_field']:
                    field_cls = sink_node['sink_field'].get(re.get_ns())
                    if not field_anno_cls or self.hierarchy_graph.is_subclass(field_anno_cls, field_cls):
                        field_anno_cls = field_cls
                for target_cls in self.closured.get(re.get_ns(), []):
                    target_cls_defi = self.def_manager.get(target_cls)
                    if target_cls_defi.get_type() == utils.constants.CLS_DEF:
                        self.hierarchy_graph.add_exist_cls_edge(self.current_ns, target_cls_defi.get_ns())

        not_exist_method = True
        if field_anno_cls:
            mod_name, cls_name = field_anno_cls.rsplit('.', 1)
            mod_node = self.module_manager.get(mod_name)
            if mod_node and field_anno_cls + '.' + func_name in mod_node.get_methods():
                not_exist_method = False

        names = self.retrieve_call_names(node)
        if not names:
            if isinstance(node.func, ast.Attribute) and self.has_ext_parent(node.func):
                # TODO: This doesn't work for cases
                # where there is an assignment of an attribute
                # i.e. import os; lala = os.path; lala.dirname()
                for name in self.get_full_attr_names(node.func):
                    ext_modname = name.split(".")[0]
                    create_ext_edge(name, ext_modname)
            elif func_name and self.is_builtin(func_name):
                name = utils.join_ns(utils.constants.BUILTIN_NAME, func_name)
                if name in self.sink_manager.get_sink_points():
                    create_ext_edge(name, utils.constants.BUILTIN_NAME)
                elif func_name == 'map':
                    for tgt_method in self.decode_node(node.args[0]):
                        if not tgt_method:
                            continue
                        self.call_graph.add_edge(self.current_method, tgt_method.get_ns())
            elif func_name and func_name in self.sink_manager.get_resource_methods():
                method_name = self.current_method.replace(self.modname + '.', '')
                mod_node = self.sink_manager.get_node(self.modname)
                sink_mod_name = None
                if not mod_node:
                    return

                if method_name in mod_node.get('sink_module_user', {}):
                    for iter_mod_name in mod_node['sink_module_user'][method_name]:
                        if iter_mod_name + '.' + func_name in self.sink_manager.get_resource_points():
                            sink_mod_name = iter_mod_name
                            break
                elif method_name in mod_node.get('sink_method_user', {}):
                    callee = mod_node['sink_method_user'][method_name]['callee']
                    if callee:
                        sink_mod_name = next(iter(callee)).split(':')[0]

                if not sink_mod_name or self.current_ns not in self.sink_manager.get_caller_sink_methods():
                    return

                if class_name != sink_mod_name and class_name in self.import_manager.get_node(self.modname)['imports']:
                    return

                sink_root_node = self.sink_manager.get_root_node(self.modname)
                if sink_root_node:
                    root_smu = sink_root_node['sink_method_user'].get(method_name)['callee']
                    if sink_mod_name + ':' + func_name not in root_smu:
                        return
                create_ext_edge(sink_mod_name + '.' + func_name, sink_mod_name)
            elif func_name and len(func_name) > 9 and func_name in self.sink_manager.get_potent_method_nodes():
                callee_mod_list = self.sink_manager.get_potent_method_node(func_name)
                sig_caller_cls = '.'.join([self.modname] + self.class_stack)
                last_mod_name = None
                if self.last_called_names:
                    for last_name in self.last_called_names:
                        if last_defi := self.def_manager.get(last_name):
                            last_mod_name = last_defi.get_module_name()
                            break
                for callee_mod in callee_mod_list:
                    if '@' in callee_mod:
                        callee_mod, method_name = callee_mod.split('@')
                        if 'kwargs' in method_name:
                            continue
                        sig_callee_cls = callee_mod + '.' + method_name.split('.')[0]
                        if (
                                (self.hierarchy_graph.have_common_parent(sig_callee_cls, sig_caller_cls)
                                 and not self.hierarchy_graph.is_subclass(sig_callee_cls, sig_caller_cls)
                                 and not self.hierarchy_graph.is_subclass(sig_caller_cls, sig_callee_cls)
                                 and sig_callee_cls != sig_caller_cls)
                                or
                                (field_anno_cls
                                 and not self.hierarchy_graph.is_subclass(sig_callee_cls, field_anno_cls)
                                 and self.hierarchy_graph.have_common_parent(sig_callee_cls, field_anno_cls))
                                or
                                (class_name == 'super'
                                 and (not self.hierarchy_graph.is_subclass(sig_caller_cls, sig_callee_cls)
                                      or sig_caller_cls == sig_callee_cls))
                                or
                                (last_mod_name and last_mod_name not in self.sink_manager.get_nodes()
                                 and func_name in self.module_manager.get(last_mod_name).get_classes_and_methods())
                        ):
                            continue
                        self.call_graph.add_edge(self.current_method, callee_mod + '.' + method_name)
            elif func_name == 'Process' and getattr(node.func.value, 'id', None) == 'multiprocessing':
                arg_fun = args_args = None
                for arg in node.keywords:
                    if arg.arg == 'target':
                        arg_fun = arg.value
                    elif arg.arg == 'args' and hasattr(arg.value, "dims"):
                        args_args = arg.value.dims
                if arg_fun and args_args:
                    call_node = ast.Call(func=arg_fun, args=args_args, keywords=[], lineno=node.lineno)
                    self.visit_Call(call_node)
            return

        if param_field and len(names) == 1:
            cls_name = next(iter(names)).rsplit('.', 1)[0]
            for subclass in self.hierarchy_graph.get_subclasses(cls_name):
                sub_meth = subclass.rsplit('.', 1)[1] + '.' + func_name
                if sub_meth in self.sink_manager.get_potent_method_nodes():
                    names.add(subclass + '.' + func_name)

        self.last_called_names = names
        for pointer in names:
            cls_name = pointer.rsplit('.', 1)[0]
            if field_anno_cls:
                if (
                        ((not self.hierarchy_graph.is_subclass(cls_name, field_anno_cls)
                          and cls_name not in field_anno_cls_set
                          and not (not_exist_method and self.hierarchy_graph.is_subclass(field_anno_cls, cls_name)))
                         and self.hierarchy_graph.have_common_parent(cls_name, field_anno_cls))
                        or (class_name == 'super' and not self.hierarchy_graph.is_subclass(sig_caller_cls, cls_name))
                ):
                    continue
                self.context_manager.set_context(pointer + '.self', self.current_ns, field_anno_cls)

                if sub_edges := self.call_graph.get_subsequent_edge(pointer):
                    for sub_edge in sub_edges.copy():
                        if field_anno_cls in sub_edge and self.current_ns != pointer:
                            pointer = self.current_ns + ':' + pointer
                            self.call_graph.add_edge(pointer, sub_edge)
                            sub_edges.remove(sub_edge)
            else:
                pass

            if class_name and receiver_is_cls and ('.' + class_name not in pointer) and (class_name in field_anno_cls):
                continue

            if class_name and ('.' + class_name in pointer) and receiver_is_cls:
                self.hierarchy_graph.add_exist_edge(self.current_method, pointer)

            if pointer in self.sink_manager.get_sink_points():
                self.local_call(node, pointer)
                self.call_graph.add_edge(self.current_method, pointer)
            pointer_def = self.def_manager.get(pointer)
            if not pointer_def or not isinstance(pointer_def, Definition):
                if ':' in pointer:
                    self.call_graph.add_edge(self.current_method, pointer)
                continue
            pointer_mod_name = pointer_def.get_module_name()
            pointer_meth_name = pointer_def.get_ns().replace(pointer_mod_name + '.', '', 1)

            if (
                    pointer_mod_name not in self.sink_manager.get_nodes()
                    or pointer_meth_name not in self.sink_manager.get_node(pointer_mod_name)["sink_method_user"]
                    or pointer_meth_name not in self.module_manager.get(pointer_mod_name).get_classes_and_methods()
            ):
                continue
            if pointer_def.is_callable():
                if pointer_def.get_type() == utils.constants.EXT_DEF:
                    ext_modname = pointer.split(".")[0]
                    create_ext_edge(pointer, ext_modname)
                    continue
                self.local_call(node, pointer)
                self.call_graph.add_edge(self.current_method, pointer)

            # TODO: This doesn't work
            # and leads to calls from the decorators
            # themselves to the function,
            # creating edges to the first decorator
            # for decorator in pointer_def.decorator_names:
            #   dec_names = self.closured.get(decorator, [])
            #   for dec_name in dec_names:
            #       if self.def_manager.get(dec_name).
            #               get_type() == utils.constants.FUN_DEF:
            #           self.call_graph.add_edge(self.current_ns, dec_name)

            if pointer_def.get_type() == utils.constants.CLS_DEF:
                init_ns = self.find_cls_fun_ns(pointer, utils.constants.CLS_INIT)
                self.call_graph.add_edge(self.current_method, pointer)

                for ns in init_ns:
                    self.local_call(node, ns)
                    self.call_graph.add_edge(self.current_method, ns)

    def visit_Return(self, node):
        self._visit_return(node)

    def visit_Yield(self, node):
        self._visit_return(node)

    def _visit_return(self, node):
        if not node or not node.value:
            return
        self.visit(node.value)
        self.is_taint(node.value, node)

    def analyze_submodules(self):
        imports = self.sink_manager.get_extra_mods()
        for imp in imports:
            self.analyze_submodule(
                CallGraphProcessor,
                imp,
                self.import_manager,
                self.scope_manager,
                self.def_manager,
                self.class_manager,
                self.module_manager,
                self.sink_manager,
                self.intersection_manager,
                self.middle_manager,
                self.context_manager,
                call_graph=self.call_graph,
                modules_analyzed=self.get_modules_analyzed(),
            )

    def analyze_submodule(self, cls, imp, *args, **kwargs):
        super().analyze_submodule(cls, imp, *args, **kwargs)

    def analyze(self):
        self.visit(ast.parse(self.contents, self.filename))
        self.analyze_submodules()

    def get_all_reachable_functions(self):
        reachable = set()
        names = set()
        current_scope = self.scope_manager.get_scope(self.current_ns)
        while current_scope:
            for name, defi in current_scope.get_defs().items():
                if defi.is_function_def() and name not in names:
                    closured = self.closured.get(defi.get_ns())
                    for item in closured:
                        reachable.add(item)
                    names.add(name)
            current_scope = current_scope.parent

        return reachable

    def has_ext_parent(self, node):
        if not isinstance(node, ast.Attribute):
            return False

        while isinstance(node, ast.Attribute):
            parents = self._retrieve_parent_names(node)
            for parent in parents:
                for name in self.closured.get(parent, []):
                    defi = self.def_manager.get(name)
                    if defi and defi.is_ext_def():
                        return True
            node = node.value
        return False

    def get_full_attr_names(self, node):
        name = ""
        while isinstance(node, ast.Attribute):
            if not name:
                name = node.attr
            else:
                name = node.attr + "." + name
            node = node.value

        names = []
        if getattr(node, "id", None) is None:
            return names

        defi = self.scope_manager.get_def(self.current_ns, node.id)
        if defi and self.closured.get(defi.get_ns()):
            for id in self.closured.get(defi.get_ns()):
                names.append(id + "." + name)

        return names

    def is_builtin(self, name):
        return name in __builtins__

    def is_taint(self, target, node):
        decoded = self.decode_node(target)
        if not decoded and hasattr(target, 'value'):
            decoded = self.decode_node(target.value)

        for d in decoded:
            if isinstance(d, list):
                for defi in d:
                    self.add_taint(defi, node)
            else:
                self.add_taint(d, node)

    def add_taint(self, defi, node):
        if isinstance(defi, Definition):
            caller_taint = self.taints.get(defi.get_ns())
            if caller_taint and any(element.startswith("Taint-Sink") for element in caller_taint):
                taint_line = "line: " + str(node.lineno)
                try:
                    stmt = ast.unparse(node)
                except Exception as e:
                    stmt = ''
                taint_stmt = "stmt: " + stmt
                if isinstance(node, ast.Call):
                    names = self.retrieve_call_names(node)
                    for p_name in names:
                        taint_stmt = taint_stmt + '@' + p_name
                        break
                taints = self.call_graph.get_taints_with_name(self.current_ns)
                if not taints:
                    self.call_graph.add_node(self.current_ns)
                    taints = self.call_graph.get_taints_with_name(self.current_ns)
                if taint_line not in taints:
                    taints[taint_line] = taint_stmt
                elif len(taint_stmt) > len(taints[taint_line]):
                    taints[taint_line] = taint_stmt
                return True

    def local_call(self, node, call_method):
        call_line = "line: " + str(node.lineno)
        calls = self.call_graph.get_edges_with_name(self.current_ns)
        if calls is None:
            return
        if call_line not in calls:
            calls[call_line] = [call_method]
        else:
            calls[call_line].append(call_method)
