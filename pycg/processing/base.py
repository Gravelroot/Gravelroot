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
import re

from pycg import utils
from pycg.machinery.definitions import Definition


class ProcessingBase(ast.NodeVisitor):
    def __init__(self, filename, modname, modules_analyzed):
        self.modname = modname

        self.modules_analyzed = modules_analyzed
        self.modules_analyzed.add(self.modname)

        self.filename = os.path.abspath(filename)

        with open(filename, "rt", errors="replace") as f:
            self.contents = f.read()

        self.name_stack = []
        self.class_stack = []
        self.method_stack = []
        self.last_called_names = None

    def get_modules_analyzed(self):
        return self.modules_analyzed

    def merge_modules_analyzed(self, analyzed):
        self.modules_analyzed = self.modules_analyzed.union(analyzed)

    @property
    def current_ns(self):
        return ".".join(self.name_stack)

    @property
    def current_method(self):
        return ".".join(self.method_stack)

    def visit_Module(self, node):
        self.name_stack.append(self.modname)
        self.method_stack.append(self.modname)
        return_scope = self.scope_manager.get_scope(self.modname)
        if not return_scope:
            self.method_stack.pop()
            self.name_stack.pop()
            return
        return_scope.reset_counters()
        self.generic_visit(node)
        if self.filename.endswith("__init__.py") and hasattr(self, "has_all_field") and not self.has_all_field:
            imports_nodes = self.import_manager.get_node(self.modname)['imports_nodes']
            for import_name, import_node in imports_nodes.items():
                if hasattr(import_node, "module"):
                    self.process_ImportFrom(import_node)
                else:
                    self.process_Import(import_node)
        self.method_stack.pop()
        self.name_stack.pop()

    def visit_FunctionDef(self, node):
        self.name_stack.append(node.name)
        self.method_stack.append(node.name)
        if self.scope_manager.get_scope(self.current_ns):
            self.scope_manager.get_scope(self.current_ns).reset_counters()
            for stmt in node.body:
                self.visit(stmt)
        self.method_stack.pop()
        self.name_stack.pop()

    def visit_Lambda(self, node, lambda_name=None):
        lambda_ns = utils.join_ns(self.current_ns, lambda_name)
        if not self.scope_manager.get_scope(lambda_ns):
            self.scope_manager.create_scope(
                lambda_ns, self.scope_manager.get_scope(self.current_ns)
            )
        self.name_stack.append(lambda_name)
        self.method_stack.append(lambda_name)
        self.visit(node.body)
        self.method_stack.pop()
        self.name_stack.pop()

    def visit_For(self, node):
        for item in node.body:
            self.visit(item)

    def visit_Dict(self, node):
        counter = node.end_lineno
        dict_name = utils.get_dict_name(counter)

        sc = self.scope_manager.get_scope(utils.join_ns(self.current_ns, dict_name))
        if not sc:
            return
        self.name_stack.append(dict_name)
        sc.reset_counters()
        for key, val in zip(node.keys, node.values):
            if key:
                self.visit(key)
            if val:
                self.visit(val)
        self.name_stack.pop()

    def visit_List(self, node):
        counter = node.end_lineno
        list_name = utils.get_list_name(counter)

        sc = self.scope_manager.get_scope(utils.join_ns(self.current_ns, list_name))
        if not sc:
            return
        self.name_stack.append(list_name)
        sc.reset_counters()
        for elt in node.elts:
            self.visit(elt)
        self.name_stack.pop()

    def visit_BinOp(self, node):
        self.visit(node.left)
        self.visit(node.right)

    def visit_ClassDef(self, node):
        self.name_stack.append(node.name)
        self.method_stack.append(node.name)
        self.class_stack.append(node.name)
        if self.scope_manager.get_scope(self.current_ns):
            self.scope_manager.get_scope(self.current_ns).reset_counters()
        for stmt in node.body:
            self.visit(stmt)
        self.class_stack.pop()
        self.method_stack.pop()
        self.name_stack.pop()

    def visit_Tuple(self, node):
        for elt in node.elts:
            self.visit(elt)

    def _handle_assign(self, targetns, decoded, isCall=True):
        defi = self.def_manager.get(targetns)
        if not defi:
            defi = self.def_manager.create(targetns, utils.constants.NAME_DEF, self.modname)

        # check if decoded is iterable
        try:
            iter(decoded)
        except TypeError:
            return defi

        idx = 0
        for d in decoded:
            if isinstance(d, list):
                self.assign_return_tuple(defi, d, idx)
                idx += 1
            elif isinstance(d, Definition) and d.get_type() == utils.constants.NAME_DEF and d.get_name() == 'UNKNOW':
                d_ns = d.get_ns().replace('.' + d.get_name(), '')
                d = self.def_manager.get(d_ns)
                for pointer in set(d.get_name_pointer().get()):
                    pointer_defi = self.def_manager.get(pointer)
                    if pointer_defi and pointer_defi.get_type() == utils.constants.FUN_DEF:
                        return_ns = utils.join_ns(
                            pointer_defi.get_ns(), utils.constants.RETURN_NAME
                        )
                        return_defi = self.def_manager.get(return_ns)
                    else:
                        return_defi = pointer_defi
                    if defi and return_defi:
                        defi.get_name_pointer().add(return_defi.get_ns())
                        return_defi.get_taint_pointer().add(defi.get_ns())
            elif isinstance(d, Definition):
                if d.get_type() == utils.constants.CLS_DEF and d.get_ns() != defi.get_ns():
                    d_met_name = d.get_ns().replace(d.get_module_name() + '.', '')
                    current_mod_classes = self.module_manager.get(d.get_module_name()).get_classes()
                    if not isCall and d_met_name in current_mod_classes:
                        defi.get_name_pointer().add(d.get_ns())
                        return defi
                    else:
                        defi.set_type(utils.constants.INS_DEF)
                if defi.get_type() == utils.constants.CLS_DEF:
                    continue
                defi.get_name_pointer().add(d.get_ns())
                d.get_taint_pointer().add(defi.get_ns())
            else:
                defi.get_lit_pointer().add(d)
        return defi

    def assign_return_tuple(self, defi, decoded, idx):
        ret_full_ns = utils.join_ns(defi.get_ns(), utils.get_ret_name(idx))
        ret_def = self.def_manager.get(ret_full_ns)
        if ret_def:
            idx_next = 0
            for d_sub in decoded:
                if not d_sub or isinstance(d_sub, (str, int, float, bool)):
                    continue
                if isinstance(d_sub, list):
                    self.assign_return_tuple(ret_def, d_sub, idx_next)
                    idx_next += 1
                else:
                    ret_def.get_name_pointer().add(d_sub.get_ns())
                    if len(re.findall(r"<r\d", ret_full_ns)) > 1:
                        ret_def.get_taint_pointer().add(defi.get_ns())
                    d_sub.get_taint_pointer().add(ret_def.get_ns())
        else:
            for d_sub in decoded:
                if not d_sub:
                    continue
                if isinstance(d_sub, Definition):
                    defi.get_name_pointer().add(d_sub.get_ns())
                else:
                    defi.get_lit_pointer().add(d_sub)

    def _visit_return(self, node):
        if not node or not node.value:
            return

        self.visit(node.value)

        return_ns = utils.join_ns(self.current_ns, utils.constants.RETURN_NAME)
        if isinstance(node.value, ast.Tuple):
            self.create_return_tuple_def(node.value.elts, return_ns)
        self._handle_assign(return_ns, self.decode_node(node.value))

    def _visit_raise(self, node):
        if not node or not node.exc:
            return

        self.visit(node.exc)
        return_ns = utils.join_ns(self.current_ns, utils.constants.EXCEPTION_NAME)
        self._handle_assign(return_ns, self.decode_node(node.exc))

    def create_return_tuple_def(self, elts, parent_ns):
        for idx, elt in enumerate(elts):
            child_ns = utils.join_ns(parent_ns, utils.get_ret_name(idx))
            if not self.def_manager.get(child_ns):
                self.def_manager.create(child_ns, utils.constants.NAME_DEF, self.modname)
            if isinstance(elt, ast.Tuple):
                self.create_return_tuple_def(elt.elts, child_ns)

    def _get_target_ns(self, target):
        if isinstance(target, ast.Name):
            return [utils.join_ns(self.current_ns, target.id)]
        if isinstance(target, ast.Attribute):
            bases = self._retrieve_base_names(target)
            res = []
            for base in bases:
                res.append(utils.join_ns(base, target.attr))
            return res
        if isinstance(target, ast.Subscript):
            return self.retrieve_subscript_names(target)
        return []

    def _visit_assign(self, value, targets):
        self.visit(value)

        isCall = True
        if isinstance(value, ast.Name):
            isCall = False

        decoded = self.decode_node(value)
        if not decoded:
            caller = None
            if hasattr(value, "func"):
                if hasattr(value.func, "value") and hasattr(value.func.value, "id"):
                    caller = value.func.value.id
                elif hasattr(value.func, "id") and value.func.id == "copy_context":
                    caller = value.func.id

                func_name = (getattr(value.func, 'attr', None) or getattr(value.func, 'id', None))
                if hasattr(self, 'middle_skip') and func_name in self.middle_skip.get(self.current_ns, set()):
                    self.is_call_middle = True

                if func_name == 'next' and not caller or caller == func_name == 'copy':
                    for arg in value.args:
                        decoded.extend(self.decode_node(arg))

                if func_name == 'getattr' and len(value.args) >= 2 and isinstance(value.args[0], ast.Name):
                    if isinstance(value.args[1], ast.Constant) and hasattr(self, 'closured'):
                        for obj in self.closured.get(self.current_ns + '.' + value.args[0].id, set()):
                            decoded.append(self.def_manager.get(obj + '.' + value.args[1].value))
            if caller:
                defi = self.def_manager.get(caller)
                if hasattr(self, "closured") and not defi:
                    defi = self.closured.get(self.current_ns + "." + caller)
                if defi:
                    if isinstance(defi, set):
                        decoded = []
                        for single_defi in defi:
                            decoded.append(self.def_manager.get(single_defi))
                    else:
                        decoded = [defi]
                elif caller in self.sink_manager.get_resource_modules() or caller == "copy_context":
                    defi = self.def_manager.create(caller, utils.constants.MOD_DEF, caller)
                    decoded = [defi]

        def do_assign(decoded, target):
            self.visit(target)
            if isinstance(target, ast.Tuple):
                for pos, elt in enumerate(target.elts):
                    if not isinstance(decoded, Definition) and pos < len(decoded):
                        do_assign(decoded[pos], elt)
            else:
                targetns = self._get_target_ns(target)
                for tns in targetns:
                    if not tns:
                        continue
                    defi = self._handle_assign(tns, decoded, isCall=isCall)
                    if defi.get_type() == utils.constants.CLS_DEF:
                        continue  # todo The assignment here needs to be changed to the instance INS_DEF
                    splitted = tns.split(".")
                    self.scope_manager.handle_assign(
                        ".".join(splitted[:-1]), splitted[-1], defi
                    )

                    if hasattr(self, 'is_call_middle') and self.is_call_middle:
                        for arg in value.args:
                            self.iter_add_taint(arg, defi)
                        for key_arg in value.keywords:
                            self.iter_add_taint(key_arg.value, defi)
                        self.is_call_middle = False

        for target in targets:
            if isinstance(target, ast.Tuple) and isinstance(value, ast.Call):
                tmp_decoded = []
                for d in decoded:
                    for idx, elt in enumerate(target.elts):
                        if isinstance(d, list):
                            continue
                        return_ns = utils.join_ns(d.get_ns(), utils.get_ret_name(idx))
                        return_def = self.def_manager.get(return_ns)
                        if not return_def:
                            d_mn = d.get_module_name()
                            return_def = self.def_manager.create(return_ns, utils.constants.NAME_DEF, d_mn)
                            d.get_taint_pointer().add(return_ns)
                        tmp_decoded.append([return_def])
                if tmp_decoded:
                    decoded = tmp_decoded
            do_assign(decoded, target)

    def decode_node(self, node):
        if isinstance(node, ast.Name):
            return [self.scope_manager.get_def(self.current_ns, node.id)]
        elif isinstance(node, ast.Call):
            decoded = self.decode_node(node.func)
            return_defs = []
            for called_def in decoded:
                if not isinstance(called_def, Definition):
                    if node.func.id == 'str':
                        return self.decode_node(node.args[0])
                    continue

                return_ns = utils.constants.INVALID_NAME
                if called_def.get_type() == utils.constants.FUN_DEF:
                    return_ns = utils.join_ns(
                        called_def.get_ns(), utils.constants.RETURN_NAME
                    )
                elif (
                        called_def.get_type() == utils.constants.CLS_DEF
                        or called_def.get_type() == utils.constants.EXT_DEF
                ):
                    return_ns = utils.join_ns(called_def.get_ns(), "__new__.<RETURN>")
                    defi = self.def_manager.get(return_ns)
                    if not defi:
                        return_ns = called_def.get_ns()
                elif called_def.get_type() == utils.constants.NAME_DEF:
                    return_ns = utils.join_ns(called_def.get_ns(), "UNKNOW")
                    if not self.def_manager.get(return_ns):
                        self.def_manager.create(return_ns, utils.constants.NAME_DEF, self.modname)
                defi = self.def_manager.get(return_ns)
                if defi:
                    return_defs.append(defi)

            return return_defs
        elif isinstance(node, ast.Lambda):
            lambda_counter = self.scope_manager.get_scope(
                self.current_ns
            ).get_lambda_counter()
            lambda_name = utils.get_lambda_name(lambda_counter)
            return [self.scope_manager.get_def(self.current_ns, lambda_name)]
        elif isinstance(node, ast.Tuple):
            decoded = []
            for elt in node.elts:
                decoded.append(self.decode_node(elt))
            return decoded
        elif isinstance(node, ast.BinOp):
            decoded_left = self.decode_node(node.left)
            decoded_right = self.decode_node(node.right)
            # return the non definition types if we're talking about a binop
            # since we only care about the type of the return (num, str, etc)
            if not isinstance(decoded_left, Definition):
                return decoded_left
            if not isinstance(decoded_right, Definition):
                return decoded_right
        elif isinstance(node, ast.Attribute):
            names = self._retrieve_attribute_names(node)
            defis = []
            for name in names:
                defi = self.def_manager.get(name)
                if defi:
                    defis.append(defi)
            return defis
        elif isinstance(node, ast.Num):
            return [node.n]
        elif isinstance(node, ast.Str):
            return [node.s]
        elif self._is_literal(node):
            return [node]
        elif isinstance(node, ast.Dict) or isinstance(node, ast.DictComp):
            dict_counter = node.end_lineno
            dict_name = utils.get_dict_name(dict_counter)
            scope_def = self.scope_manager.get_def(self.current_ns, dict_name)
            return [scope_def]
        elif isinstance(node, ast.List):
            list_counter = node.end_lineno
            list_name = utils.get_list_name(list_counter)
            scope_def = self.scope_manager.get_def(self.current_ns, list_name)
            return [scope_def]
        elif isinstance(node, ast.Subscript):
            names = self.retrieve_subscript_names(node)
            defis = []
            for name in names:
                defi = self.def_manager.get(name)
                if defi:
                    defis.append(defi)
            return defis
        elif isinstance(node, ast.Starred):
            defis = []
            if hasattr(node.value, 'id'):
                defi = self.scope_manager.get_def(self.current_ns, node.value.id)
                if defi:
                    defis.append(defi)
            return defis
        elif isinstance(node, ast.BoolOp):
            defis = []
            for value in getattr(node, 'values', []):
                if defi := self.decode_node(value):
                    defis.append(defi)
            return defis
        elif isinstance(node, ast.IfExp):
            defis = []
            if hasattr(node, 'body'):
                defi_1 = self.decode_node(node.body)
                if defi_1:
                    defis.append(defi_1)
            if hasattr(node, 'orelse'):
                defi_2 = self.decode_node(node.orelse)
                if defi_2:
                    defis.append(defi_2)
            return defis
        return []

    def _is_literal(self, item):
        return isinstance(item, int) or isinstance(item, str) or isinstance(item, float)

    def _retrieve_base_names(self, node):
        if not isinstance(node, ast.Attribute):
            raise Exception("The node is not an attribute")

        if not getattr(self, "closured", None):
            return set()

        decoded = self.decode_node(node.value)
        if not decoded:
            return set()

        names = set()
        for name in decoded:
            if not name or not isinstance(name, Definition):
                continue

            for base in self.closured.get(name.get_ns(), []):
                cls = self.class_manager.get(base)
                if not cls:
                    continue

                for item in cls.get_mro():
                    names.add(item)
        return names

    def _retrieve_parent_names(self, node):
        if not isinstance(node, ast.Attribute):
            raise Exception("The node is not an attribute")

        decoded = self.decode_node(node.value)
        if not decoded:
            return set()

        names = set()
        for parent in decoded:
            if not parent or not isinstance(parent, Definition):
                continue
            if getattr(self, "closured", None) and self.closured.get(
                    parent.get_ns(), None
            ):
                names = names.union(self.closured.get(parent.get_ns()))
            else:
                names.add(parent.get_ns())
        return names

    def _retrieve_attribute_names(self, node):
        if not getattr(self, "closured", None):
            return set()

        analyzed_list = set()

        parent_names = self._retrieve_parent_names(node)
        names = set()
        for parent_name in parent_names:
            for name in self.closured.get(parent_name, []):
                if name in analyzed_list:
                    continue
                defi = self.def_manager.get(name)
                analyzed_list.add(name)
                if not defi:
                    continue
                if defi.get_type() == utils.constants.CLS_DEF or defi.get_type() == utils.constants.INS_DEF:
                    cls_names = self.find_cls_fun_ns(defi.get_ns(), node.attr)
                    if cls_names:
                        names = names.union(cls_names)
                if defi.get_type() in [
                    utils.constants.FUN_DEF,
                    utils.constants.MOD_DEF,
                ]:
                    names.add(utils.join_ns(name, node.attr))
                if defi.get_type() == utils.constants.EXT_DEF:
                    # HACK: extenral attributes can lead to infinite loops
                    # Identify them here
                    if node.attr in name:
                        continue
                    ext_name = utils.join_ns(name, node.attr)
                    if not self.def_manager.get(ext_name):
                        self.def_manager.create(ext_name, utils.constants.EXT_DEF)
                    names.add(ext_name)
        return names

    def iterate_call_args(self, defi, node):
        for pos, arg in enumerate(node.args):
            self.visit(arg)
            decoded = self.decode_node(arg)
            if defi.is_function_def():
                if isinstance(arg, ast.Starred):
                    starred_contain_count = len(defi.get_name_pointer().get_pos_names()) - pos - len(node.keywords)
                    for i in range(starred_contain_count):
                        pos_arg_names = defi.get_name_pointer().get_pos_arg(pos + i)
                        if not pos_arg_names:
                            continue
                        if not decoded and isinstance(arg, ast.Attribute):
                            self.construct_obj_arg_taint_edge(arg, pos_arg_names)
                        else:
                            self.construct_arg_pos_edge(pos_arg_names, decoded)
                else:
                    pos_arg_names = defi.get_name_pointer().get_pos_arg(pos)
                    # if arguments for this position exist update their namespace
                    if not pos_arg_names:
                        continue
                    if not decoded and isinstance(arg, ast.Attribute):
                        self.construct_obj_arg_taint_edge(arg, pos_arg_names)
                    else:
                        self.construct_arg_pos_edge(pos_arg_names, decoded)
            else:
                for d in decoded:
                    if isinstance(d, Definition):
                        defi.get_name_pointer().add_pos_arg(pos, None, d.get_ns())
                    else:
                        defi.get_name_pointer().add_pos_lit_arg(pos, None, d)

        for keyword in node.keywords:
            self.visit(keyword.value)
            decoded = self.decode_node(keyword.value)
            if defi.is_function_def():
                arg_names = defi.get_name_pointer().get_arg(keyword.arg) or defi.get_name_pointer().get_arg('kwargs')
                if not arg_names:
                    continue

                if not decoded and isinstance(keyword.value, ast.Attribute):
                    self.construct_obj_arg_taint_edge(keyword.value, arg_names)
                else:
                    self.construct_arg_pos_edge(arg_names, decoded)
            else:
                for d in decoded:
                    if isinstance(d, Definition):
                        defi.get_name_pointer().add_arg(keyword.arg, d.get_ns())
                    else:
                        defi.get_name_pointer().add_lit_arg(keyword.arg, d)

    def construct_obj_arg_taint_edge(self, node, arg_names):
        for name in arg_names:
            arg_def = self.def_manager.get(name)
            if not arg_def:
                continue
            decoded = self.decode_node(node.value)
            for d in decoded:
                if isinstance(d, Definition):
                    d.get_taint_pointer().add(arg_def.get_ns())

    def construct_arg_pos_edge(self, arg_names, decoded):
        for name in arg_names:
            arg_def = self.def_manager.get(name)
            if not arg_def:
                continue
            for d in decoded:
                if isinstance(d, Definition):
                    arg_def.get_name_pointer().add(d.get_ns())
                    d.get_taint_pointer().add(arg_def.get_ns())
                else:
                    arg_def.get_lit_pointer().add(d)

    def retrieve_subscript_names(self, node):
        if not isinstance(node, ast.Subscript):
            raise Exception("The node is not an subcript")

        if not getattr(self, "closured", None):
            return set()

        if getattr(node.slice, "value", None) and self._is_literal(node.slice.value):
            sl_names = [node.slice.value]
        else:
            sl_names = self.decode_node(node.slice)

        val_names = self.decode_node(node.value)

        decoded_vals = set()
        keys = set()
        full_names = set()
        # get all names associated with this variable name
        for n in val_names:
            if n and isinstance(n, Definition) and self.closured.get(n.get_ns(), None):
                decoded_vals |= self.closured.get(n.get_ns())
        for s in sl_names:
            if isinstance(s, Definition) and self.closured.get(s.get_ns(), None):
                # we care about the literals pointed by the name
                # not the namespaces, so retrieve the literals pointed
                for name in self.closured.get(s.get_ns()):
                    defi = self.def_manager.get(name)
                    if not defi:
                        continue
                    keys |= defi.get_lit_pointer().get()
            elif isinstance(s, str):
                keys.add(s)
            elif isinstance(s, int):
                keys.add(utils.get_int_name(s))

        for d in decoded_vals:
            for key in keys:
                # check for existence of var name and key combination
                str_key = str(key)
                if isinstance(key, int):
                    str_key = utils.get_int_name(key)
                if re.search(r'<dict\d+>$', d) is not None:
                    full_ns = utils.join_ns(d, str_key)
                    full_names.add(full_ns)
            if not keys:
                if re.search(r'<dict\d+>$', d) is not None:
                    full_names.clear()
                    full_names.add(d + '.<all>')
                    break
                else:
                    full_names.add(d)
        return full_names

    def retrieve_call_names(self, node):
        names = set()
        if isinstance(node.func, ast.Name):
            defi = self.scope_manager.get_def(self.current_ns, node.func.id)
            if defi:
                names = self.closured.get(defi.get_ns(), [])
                for parent_name in names:
                    if (defi.get_ns().endswith(".self") or defi.get_type() == utils.constants.INS_DEF):
                        cls_names = self.find_cls_fun_ns(parent_name, utils.constants.CALL_Method)
                        names = names.union(cls_names)
        elif isinstance(node.func, ast.Call) and self.last_called_names:
            for name in self.last_called_names:
                return_ns = utils.join_ns(name, utils.constants.RETURN_NAME)
                returns = self.closured.get(return_ns)
                if not returns:
                    continue
                for ret in returns:
                    defi = self.def_manager.get(ret)
                    names.add(defi.get_ns())
        elif isinstance(node.func, ast.Attribute):
            names = self._retrieve_attribute_names(node.func)
            if "copy_context.run" in names and len(node.args) > 0:
                decoded = self.decode_node(node.args[0])
                for d in decoded:
                    def_name = d.get_ns() if isinstance(d, Definition) else d
                    if point_value := self.determine_arg_in_sink(def_name):
                        names.add(point_value)
        elif isinstance(node.func, ast.Subscript):
            # Calls can be performed only on single indices, not ranges
            full_names = self.retrieve_subscript_names(node.func)
            for n in full_names:
                if self.closured.get(n, None):
                    names |= self.closured.get(n)
                defi = self.def_manager.get(n)
                if defi and defi.get_type() == utils.constants.INS_DEF:
                    for parent_name in defi.get_name_pointer().get():
                        cls_names = self.find_cls_fun_ns(parent_name, utils.constants.CALL_Method)
                        names = names.union(cls_names)

        return names

    def analyze_submodules(self, cls, *args, **kwargs):
        imports = self.import_manager.get_imports(self.modname)

        for imp in imports:
            self.analyze_submodule(cls, imp, *args, **kwargs)

    def analyze_submodule(self, cls, imp, *args, **kwargs):
        if imp in self.get_modules_analyzed():
            return

        fname = self.import_manager.get_filepath(imp)

        if (
                not fname
                or not fname.endswith(".py")
                or self.import_manager.get_mod_dir() not in fname
        ):
            return

        self.import_manager.set_current_mod(imp, fname)
        visitor = cls(fname, imp, *args, **kwargs)
        visitor.analyze()
        self.merge_modules_analyzed(visitor.get_modules_analyzed())

        self.import_manager.set_current_mod(self.modname, self.filename)

    def find_cls_fun_ns(self, cls_name, fn):
        cls = self.class_manager.get(cls_name)
        if not cls:
            return set()

        ext_names = set()
        for item in cls.get_mro():
            ns = utils.join_ns(item, fn)
            names = set()
            if getattr(self, "closured", None) and self.closured.get(ns, None):
                names = self.closured[ns]
            else:
                names.add(ns)

            if self.def_manager.get(ns):
                return names

            parent = self.def_manager.get(item)
            if parent and parent.get_type() == utils.constants.EXT_DEF:
                ext_names.add(ns)

        for name in ext_names:
            self.def_manager.create(name, utils.constants.EXT_DEF)
            self.add_ext_mod_node(name)
        return ext_names

    def add_ext_mod_node(self, name):
        ext_modname = name.split(".")[0]
        ext_mod = self.module_manager.get(ext_modname)
        if not ext_mod:
            ext_mod = self.module_manager.create(ext_modname, None, external=True)
            ext_mod.add_method(ext_modname)

        ext_mod.add_method(name)

    def extract_and_store_potential_methods(self, current_ns, modname, middle_node, is_local):
        middle_method_string = current_ns
        mod_method = modname + ':' + current_ns
        while True:
            init_temp = {'callee': set(), 'caller': set()}
            last_dot_index = middle_method_string.rfind('.')
            if last_dot_index == -1:
                break
            middle_method_string = middle_method_string[:last_dot_index]
            if is_local:
                middle_method_string += '-l'
            middle_node["potent_method"].setdefault(middle_method_string, init_temp)['callee'].add(mod_method)
            self.middle_manager.add_potent_method_node(middle_method_string, {modname})

    def extract_and_store_potential_sink_methods(self, current_ns, modname, sink_node):
        method_string = current_ns
        mod_method = modname + ':' + current_ns
        while True:
            init_temp = {'callee': set(), 'caller': set()}
            last_dot_index = method_string.rfind('.')
            if last_dot_index == -1:
                break
            suffix_string = method_string[last_dot_index + 1:]
            method_string = method_string[:last_dot_index]
            if current_ns in sink_node['sink_method_user']:
                sink_node['sink_method_user'].setdefault(method_string, init_temp)['callee'].add(mod_method)
                sink_node['sink_method_user'][current_ns]['caller'].add(modname + ':' + method_string)
                self.sink_manager.add_potent_method_node(method_string, {modname})
                if len(suffix_string) > 9:
                    self.sink_manager.add_potent_method_node(suffix_string, {modname + '@' + current_ns})

    def extract_and_store_potential_sink_modules(self, current_ns, sink_node):
        method_string = current_ns
        module_set = sink_node['sink_module_user'].get(method_string, set())
        while True:
            last_dot_index = method_string.rfind('.')
            if last_dot_index == -1:
                break
            suffix = method_string[last_dot_index + 1:]
            if len(suffix) < 9 or method_string.endswith('__init__'):
                method_string = method_string[:last_dot_index]
            else:
                method_string = suffix
            if module_set:
                sink_node['sink_module_user'].setdefault(method_string, set()).update(module_set)
                self.sink_manager.add_potent_module_node(method_string, module_set)
                self.sink_manager.add_module_nodes_mod(method_string, {self.modname})

    def init_sink_node(self):
        self.sink_manager.create_node(self.modname)
        self.sink_manager.set_filepath(self.modname, self.filename)
        get_module = self.module_manager.get(self.modname)
        if get_module:
            caller_message = get_module.get_caller_messages()
            self.sink_manager.update_caller_message(self.modname, caller_message)

    def determine_arg_in_sink(self, def_name):
        if isinstance(def_name, list):
            return
        point_values = self.closured.get(def_name, [])
        for point_value in point_values:
            mod_name = self.def_manager.get(point_value).get_module_name()
            part_name = point_value.replace(mod_name + '.', '')
            if (
                    mod_name in self.sink_manager.get_nodes()
                    and
                    (
                            part_name in self.sink_manager.get_potent_method_nodes()
                            or part_name in self.sink_manager.get_node(mod_name)['sink_method_user']
                    )
            ):
                return point_value
        return None
