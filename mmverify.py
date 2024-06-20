#!/usr/bin/env python3
"""mmverify.py -- Proof verifier for the Metamath language
Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
Copyright (C) David A. Wheeler and mmverify.py contributors

This program is free software distributed under the MIT license;
see the file LICENSE for full license information.
SPDX-License-Identifier: MIT

To run the program, type
  $ python3 mmverify.py set.mm --logfile set.log
and set.log will have the verification results.  One can also use bash
redirections and type '$ python3 mmverify.py < set.mm 2> set.log' but this
would fail in case 'set.mm' contains (directly or not) a recursive inclusion
statement $[ set.mm $] .

To get help on the program usage, type
  $ python3 mmverify.py -h

(nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
after a $e hypothesis in the same scope, even though this is allowed by
the Metamath spec.  This is not a serious limitation since it can be
met by rearranging the hypothesis order.
(rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
(sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
and file inclusion
(bj 3-Apr-2022) streamlined code; obtained significant speedup (4x on set.mm)
by verifying compressed proofs without converting them to normal proof format;
added type hints
(am 29-May-2023) added typeguards
"""

import re
import sys
import itertools
import pathlib
import argparse
import typing
import io
import copy

Label = str
Var = str
Const = str
Stmttype = typing.Literal["$c", "$v", "$f", "$e", "$a", "$p", "$d", "$="]
StringOption = typing.Optional[str]
Symbol = typing.Union[Var, Const]
Stmt = list[Symbol]
Ehyp = Stmt
Fhyp = tuple[Const, Var]
Dv = tuple[Var, Var]
Assertion = tuple[set[Dv], list[Fhyp], list[Ehyp], Stmt]
FullStmt = tuple[Stmttype, typing.Union[Stmt, Assertion]]

def is_hypothesis(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Stmt]]:
    """The second component of a FullStmt is a Stmt when its first
    component is '$e' or '$f'."""
    return stmt[0] in ('$e', '$f')

def is_assertion(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Assertion]]:
    """The second component of a FullStmt is an Assertion if its first
    component is '$a' or '$p'."""
    return stmt[0] in ('$a', '$p')

# Note: a script at github.com/metamath/set.mm removes from the following code
# the lines beginning with (spaces followed by) 'vprint(' using the command
#   $ sed -E '/^ *vprint\(/d' mmverify.py > mmverify.faster.py
# In order that mmverify.faster.py be valid, one must therefore not break
# 'vprint' commands over multiple lines, nor have indented blocs containing
# only vprint lines (this would create ill-indented files).


class MMError(Exception):
    """Class of Metamath errors."""
    pass


class MMKeyError(MMError, KeyError):
    """Class of Metamath key errors."""
    pass


def vprint(vlevel: int, *arguments: typing.Any) -> None:
    """Print log message if verbosity level is higher than the argument."""
    if verbosity >= vlevel:
        print(*arguments, file=logfile)


class Toks:
    """Class of sets of tokens from which functions read as in an input
    stream.
    """

    def __init__(self, file: io.TextIOWrapper) -> None:
        """Construct a 'Toks' from the given file: initialize a line buffer
        containing the lines of the file, and initialize a set of imported
        files to a singleton containing that file, so as to avoid multiple
        imports.
        """
        self.files_buf = [file]
        self.tokbuf: list[str] = []
        self.imported_files = set({pathlib.Path(file.name).resolve()})

    def read(self) -> StringOption:
        """Read the next token in the token buffer, or if it is empty, split
        the next line into tokens and read from it."""
        while not self.tokbuf:
            if self.files_buf:
                line = self.files_buf[-1].readline()
            else:
                # There is no file to read from: this can only happen if end
                # of file is reached while within a ${ ... $} block.
                raise MMError("Unclosed ${ ... $} block at end of file.")
            if line:  # split the line into a list of tokens
                self.tokbuf = line.split()
                self.tokbuf.reverse()
            else:  # no line: end of current file
                self.files_buf.pop().close()
                if not self.files_buf:
                    return None  # End of database
        tok = self.tokbuf.pop()
        vprint(90, "Token:", tok)
        return tok

    def readf(self) -> StringOption:
        """Read the next token once included files have been expanded.  In the
        latter case, the path/name of the expanded file is added to the set of
        imported files so as to avoid multiple imports.
        """
        tok = self.read()
        while tok == '$[':
            filename = self.read()
            if not filename:
                raise MMError(
                    "Unclosed inclusion statement at end of file.")
            endbracket = self.read()
            if endbracket != '$]':
                raise MMError(
                    ("Inclusion statement for file {} not " +
                     "closed with a '$]'.").format(filename))
            file = pathlib.Path(filename).resolve()
            if file not in self.imported_files:
                # wrap the rest of the line after the inclusion command in a
                # file object
                self.files_buf.append(
                    io.StringIO(
                        " ".join(
                            reversed(
                                self.tokbuf))))
                self.tokbuf = []
                self.files_buf.append(open(file, mode='r', encoding='ascii'))
                self.imported_files.add(file)
                vprint(5, 'Importing file:', filename)
            tok = self.read()
        vprint(80, "Token once included files expanded:", tok)
        return tok

    def readc(self) -> StringOption:
        """Read the next token once included files have been expanded and
        comments have been skipped.
        如果读到注释,一直读入直到发现结束符$)时停止,
        """
        tok = self.readf()
        while tok == '$(':
            # Note that we use 'read' in this while-loop, and not 'readf',
            # since inclusion statements within a comment are still comments
            # so should be skipped.
            # The following line is not necessary but makes things clearer;
            # note the similarity with the first three lines of 'readf'.
            tok = self.read()
            while tok and tok != '$)':
                if '$(' in tok or '$)' in tok:
                    raise MMError(
                        ("Encountered token '{}' while reading a comment. " +
                         "Comment contents should not contain '$(' nor " +
                         "'$)' as a substring.  In particular, comments " +
                         "should not nest.").format(tok))
                tok = self.read()
            if not tok:
                raise MMError("Unclosed comment at end of file.")
            assert tok == '$)'
            # 'readf' since an inclusion may follow a comment immediately
            tok = self.readf()
        vprint(70, "Token once comments skipped:", tok)
        return tok


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self) -> None:
        """Construct an empty frame."""
        self.v: set[Var] = set()
        self.d: set[Dv] = set()
        self.f: list[Fhyp] = []
        self.f_labels: dict[Var, Label] = {}
        self.e: list[Ehyp] = []
        self.e_labels: dict[tuple[Symbol, ...], Label] = {}
        # Note: both self.e and self.e_labels are needed since the keys of
        # self.e_labels form a set, but the order and repetitions of self.e
        # are needed.

    def __str__(self):
        return f"Frame(v={self.v}, d={self.d}, f={self.f}, f_labels={self.f_labels}, " \
               f"e={self.e}, e_labels={self.e_labels})"

class FrameStack(list[Frame]):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self) -> None:
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_e(self, stmt: Stmt, label: Label) -> None:
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        frame = self[-1]
        frame.e.append(stmt)
        frame.e_labels[tuple(stmt)] = label
        # conversion to tuple since dictionary keys must be hashable

    def add_d(self, varlist: list[Var]) -> None:
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        self[-1].d.update((min(x, y), max(x, y))
                          for x, y in itertools.product(varlist, varlist)
                          if x != y)

    def lookup_v(self, tok: Var) -> bool:
        """Return whether the given token is an active variable."""
        return any(tok in fr.v for fr in self)

    def lookup_d(self, x: Var, y: Var) -> bool:
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x, y), max(x, y)) in fr.d for fr in self)

    def lookup_f(self, var: Var) -> typing.Optional[Label]:
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.f_labels[var]
            except KeyError:
                pass
        return None  # Variable is not actively typed

    def lookup_e(self, stmt: Stmt) -> Label:
        """Return the label of the (earliest) active essential hypothesis with
        the given statement.
        """
        stmt_t = tuple(stmt)
        for frame in self:
            try:
                return frame.e_labels[stmt_t]
            except KeyError:
                pass
        raise MMKeyError(stmt_t)

    def find_vars(self, stmt: Stmt) -> set[Var]:
        """Return the set of variables in the given statement."""
        return {x for x in stmt if self.lookup_v(x)}

    def make_assertion(self, stmt: Stmt) -> Assertion:
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.e]
        mand_vars = {tok for hyp in itertools.chain(e_hyps, [stmt])
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y)
               in fr.d if x in mand_vars and y in mand_vars}
        f_hyps = []
        for fr in self:
            for typecode, var in fr.f:
                if var in mand_vars:
                    f_hyps.append((typecode, var))
                    mand_vars.remove(var)
        assertion = dvs, f_hyps, e_hyps, stmt
        # vprint(18, 'Make assertion:', assertion)
        return assertion

    def get_hyps(self) -> tuple[set[tuple[Var, Var]],list,list[Ehyp]]:
        """不知道要证明的断言, 返回依赖和假设dvs, f_hyps, e_hyps
        将前面定义的内容全部作为假设（当作全部都有可能用到）
        (和make_assertion功能类似, 只是make_assersion只是取了要证明的断言中用到的假设)
        """
        e_hyps = [eh for fr in self for eh in fr.e]
        mand_vars = {tok for hyp in itertools.chain(e_hyps)  #去掉stmt的迭代，还是重新换一个用了全部变量的迭代？ 试一下去掉
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y)
               in fr.d if x in mand_vars and y in mand_vars}
        f_hyps = []
        for fr in self:
            for typecode, var in fr.f:
                if var in mand_vars:
                    f_hyps.append((typecode, var))
                    mand_vars.remove(var)

        vprint(18, 'dvs, f_hyps, e_hyps:', dvs, f_hyps, e_hyps)
        return dvs, f_hyps, e_hyps



def apply_subst(stmt: Stmt, subst: dict[Var, Stmt]) -> Stmt:
    """Return the token list resulting from the given substitution
    (dictionary) applied to the given statement (token list).
    """
    result = []
    for tok in stmt:
        if tok in subst:
            result += subst[tok]
        else:
            result.append(tok)
    # vprint(20, 'Applying subst', subst, 'to stmt', stmt, ':', result)
    return result



class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label: Label, stop_label: Label) -> None:
        """Construct an empty Metamath database."""
        self.constants: set[Const] = set()
        self.fs = FrameStack()
        self.labels: dict[Label, FullStmt] = {}
        self.begin_label = begin_label
        self.stop_label = stop_label
        self.verify_proofs = not self.begin_label

        self.backup_constants: set[Const] = set()
        self.backup_fs = FrameStack()
        self.backup_labels: dict[Label, FullStmt] = {}
        self.backup_begin_label = begin_label
        self.backup_stop_label = stop_label
        self.backup_verify_proofs = not self.begin_label

    def MM_add(self, **arg):
        pass
    def roll_back(self,print:bool = True):
        self.constants = copy.deepcopy(self.backup_constants)
        self.fs = copy.deepcopy(self.backup_fs)
        self.labels = copy.deepcopy(self.backup_labels)
        self.begin_label = copy.deepcopy(self.backup_begin_label)
        self.stop_label = copy.deepcopy(self.backup_stop_label)
        self.verify_proofs = copy.deepcopy(self.backup_verify_proofs)

        # if print:
        #     print(self)

    def update_backup(self):
        self.backup_constants = copy.deepcopy(self.constants)
        self.backup_fs = copy.deepcopy(self.fs)
        self.backup_labels = copy.deepcopy(self.labels)
        self.backup_begin_label = copy.deepcopy(self.begin_label)
        self.backup_stop_label = copy.deepcopy(self.stop_label)
        self.backup_verify_proofs = copy.deepcopy(self.verify_proofs)

    def handle_error(self, mes, file=sys.stderr):
        print(mes, file=file)
        self.roll_back()

    def add_c(self, tok: Const) -> bool:
        """Add a constant to the database."""
        if tok in self.constants:
            self.handle_error('Constant already declared: {}'.format(tok))
            return False
            # raise MMError('Constant already declared: {}'.format(tok))

        if self.fs.lookup_v(tok):
            self.handle_error('Trying to declare as a constant an active variable: {}'.format(tok))
            return False
            # raise MMError('Trying to declare as a constant an active variable: {}'.format(tok))

        self.constants.add(tok)
        self.update_backup()

        return True

    def add_v(self, tok: Var) -> bool:
        """Add a variable to the frame stack top (that is, the current frame)
        of the database.  Allow local variable declarations.
        """
        if self.fs.lookup_v(tok):
            self.handle_error('var already declared and active: {}'.format(tok))
            return False
            # raise MMError('var already declared and active: {}'.format(tok))

        if tok in self.constants:
            self.handle_error('var already declared as constant: {}'.format(tok))
            return False
            # raise MMError('var already declared as constant: {}'.format(tok))

        self.fs[-1].v.add(tok)
        self.update_backup()
        return True

    def add_f(self, typecode: Const, var: Var, label: Label) -> bool:
        """Add a floating hypothesis (ordered pair (variable, typecode)) to
        the frame stack top (that is, the current frame) of the database.
        """
        if not self.fs.lookup_v(var):
            self.handle_error('var in $f not declared: {}'.format(var))
            return False

        if typecode not in self.constants:
            self.handle_error('typecode in $f not declared: {}'.format(typecode))
            return False

        if any(var in fr.f_labels for fr in self.fs):
            self.handle_error(
                ("var in $f already typed by an active " +
                 "$f-statement: {}").format(var))
            return False

        frame = self.fs[-1]
        frame.f.append((typecode, var))
        frame.f_labels[var] = label
        self.update_backup()
        return True

    def readstmt_aux(
            self,
            stmttype: Stmttype,
            toks: Toks,
            end_token: str) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        statement) and return the list of tokens until the end_token
        (typically "$=" or "$.").
        作用应该是解析读入的token
        """
        stmt = []
        tok = toks.readc()  # 检测是否是comment如果是就跳过;检测comment格式是否正确
        while tok and tok != end_token:
            is_active_var = self.fs.lookup_v(tok)
            if stmttype in {'$d', '$e', '$a', '$p'} and not (
                    tok in self.constants or is_active_var):
                raise MMError(
                    "Token {} is not an active symbol".format(tok))
            if stmttype in {
                '$e',
                '$a',
                    '$p'} and is_active_var and not self.fs.lookup_f(tok):
                raise MMError(("Variable {} in {}-statement is not typed " +
                               "by an active $f-statement).").format(tok, stmttype))
            stmt.append(tok)
            vprint(1,f"statement: {stmt}")
            tok = toks.readc()
        if not tok:
            raise MMError(
                "Unclosed {}-statement at end of file.".format(stmttype))
        assert tok == end_token
        vprint(20, 'Statement:', stmt)
        return stmt

    def read_proof_and_calculate(
            self,
            stmttype: Stmttype,
            toks: Toks,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            end_token: str
            ) -> None:
        """读取证明序列并进行每一步的正确计算, 若证明步骤未声明或栈操作出错则报错
        若读到'jumpn' 跳转到第n步"""
        vprint(3,'[read_proof_and_calculate(stmttype,toks,end_token,f_hyps,e_hyps)]:',stmttype,toks,end_token,f_hyps,e_hyps)
        stmt = []
        tok = toks.readc()  # 检测是否是comment如果是就跳过;检测comment格式是否正确
        normal_flag = True  # 是否是正常格式证明
        stack: list[Stmt] = []  # 初始化证明栈
        stacks: list[list[Stmt]] = [[]]   # 每一步的证明栈
        jump_pattern = r'jump(\d+)'   # 跳转步骤命令 e.g., jump3  jump2
        step_int = 0   # 当前证明步骤序号
        if tok == '(' : #若proof第一个tok是 '('则为压缩格式证明
            normal_flag = False
        # 压缩格式还没有写

        while tok and tok != end_token: # 未读完且并当前tok不等于 end_token
            is_active_var = self.fs.lookup_v(tok)
            if stmttype in {'$d', '$e', '$a', '$p'} and not (
                    tok in self.constants or is_active_var):
                self.handle_error("Token {} is not an active symbol".format(tok))
                # raise MMError(
                #     "Token {} is not an active symbol".format(tok))
            if stmttype in {
                '$e',
                '$a',
                    '$p'} and is_active_var and not self.fs.lookup_f(tok):
                self.handle_error(("Variable {} in {}-statement is not typed " +
                               "by an active $f-statement).").format(tok, stmttype))
            
            if re.search(jump_pattern, tok): # 如果读到 jump命令
                jump_int = int(re.search(jump_pattern, tok).group(1))
                vprint(30,'jump to Step',jump_int)
               
                if jump_int <= step_int:
                    if normal_flag: 
                        tok = stmt[jump_int-1]
                        stmt = stmt[:jump_int-1]
                    else:
                        # tok = stmt[jump_int + idx_bloc]
                        # stmt = stmt[:jump_int + idx_bloc]
                        pass ##压缩格式待写
                    if jump_int == 1:
                        stacks = [[]]
                    else:
                        stacks = stacks[:jump_int]
                        stacks[jump_int-1] = stacks[jump_int-2].copy()
                    # print('tok:',tok)
                    # print('Stmt jump to:',stmt)
                    # print('stacks jump:',stacks)
                else:
                    self.handle_error(("Jump error: The number of steps cannot be greater than the current number of steps {}.").format(step_int))
            
            if normal_flag: # 正常格式证明序列
                step_int = len(stmt) + 1 
                correct_flag,stack = self.verify_and_calculate_proof_step_normal(f_hyps,e_hyps,tok,stacks[step_int-1],step_int)  #正确计算并更新栈状态
                if len(stacks) <= step_int:
                    stacks.append(stack.copy())
                    # print('stacks',stacks)
                else:
                    stacks[step_int] = stack.copy()
                if correct_flag:  # 当前证明步骤若正确 新增步骤
                    stmt.append(tok)  # stmt 索引就是证明步骤序号
            else:
                pass ##压缩格式待写

            tok = toks.readc()   ##下一个token

        if not tok:  # 证明序列读取结束
            self.handle_error("Unclosed {}-statement at end of file.".format(stmttype))
            # raise MMError(
            #     "Unclosed {}-statement at end of file.".format(stmttype))
        assert tok == end_token

        vprint(20, 'Statement:', stmt)  
        vprint(10, 'Current stack of proof-:', stack)
        # if not stack:
        #     self.handle_error("Empty stack at end of proof.")
        self.update_backup()
        vprint(3, 'Calculate finish!')


    def read_proof_and_verify(
            self,
            stmttype: Stmttype,
            toks: Toks,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            end_token: str
            ) -> None:
        """读取证明序列并进行每一步的验证 
        若读到'jumpn' 跳转到第n步      
                    """
        #(循环时对每一步验证) 
        vprint(3,'[read_proof_and_verify(stmttype,toks,end_token,f_hyps,e_hyps,conclusion)]:',stmttype,toks,end_token,f_hyps,e_hyps,conclusion)
        stmt = []
        tok = toks.readc()  # 检测是否是comment如果是就跳过;检测comment格式是否正确
        normal_flag = True  # 是否是正常格式证明
        stack: list[Stmt] = []  # 初始化证明栈
        stacks: list[list[Stmt]] = [[]]   # 每一步的证明栈
        jump_pattern = r'jump(\d+)'   # 跳转步骤命令 e.g., jump3  jump2
        step_int = 0   # 当前证明步骤序号
        if tok == '(' : #若proof第一个tok是 '('则为压缩格式证明
            normal_flag = False

        # 验证压缩格式证明序列 参数初始化 start---------------
        flabels = [self.fs.lookup_f(v) for _, v in f_hyps]
        elabels = [self.fs.lookup_e(s) for s in e_hyps]
        plabels = flabels + elabels  # labels of implicit hypotheses  
        if not normal_flag:
            vprint(3,'flabels:',flabels)
            vprint(3,'elabel:',elabels)
            vprint(3,'plabel:',plabels)
        label_end = 0
        # statements saved for later reuse (marked with a 'Z')
        saved_stmts = []
        # can be recovered as len(saved_stmts) but less efficient
        n_saved_stmts = 0
        end_flag = False   # 是否读完引理
        # 验证压缩格式证明序列 参数初始化 end---------------
        

        while tok and tok != end_token: # 未读完且并当前tok不等于 end_token
            is_active_var = self.fs.lookup_v(tok)
            if stmttype in {'$d', '$e', '$a', '$p'} and not (
                    tok in self.constants or is_active_var):
                self.handle_error("Token {} is not an active symbol".format(tok))
                # raise MMError(
                #     "Token {} is not an active symbol".format(tok))
            if stmttype in {
                '$e',
                '$a',
                    '$p'} and is_active_var and not self.fs.lookup_f(tok):
                self.handle_error(("Variable {} in {}-statement is not typed " +
                               "by an active $f-statement).").format(tok, stmttype))
                # raise MMError(("Variable {} in {}-statement is not typed " +
                #                "by an active $f-statement).").format(tok, stmttype))
           
            
            # self.verify(f_hyps,e_hyps,conclusion,stmt,False) #对当前stmt的verify
        
            if re.search(jump_pattern, tok): # 如果读到 jump命令
                jump_int = int(re.search(jump_pattern, tok).group(1))
                vprint(30,'jump to Step',jump_int)
               
                if jump_int <= step_int:
                    if normal_flag: 
                        tok = stmt[jump_int-1]
                        stmt = stmt[:jump_int-1]
                    else:
                        tok = stmt[jump_int + idx_bloc]
                        stmt = stmt[:jump_int + idx_bloc]
                    if jump_int == 1:
                        stacks = [[]]
                    else:
                        stacks = stacks[:jump_int]
                        stacks[jump_int-1] = stacks[jump_int-2].copy()
                    # print('tok:',tok)
                    # print('Stmt jump to:',stmt)
                    # print('stacks jump:',stacks)
                else:
                    self.handle_error(("Jump error: The number of steps cannot be greater than the current number of steps {}.").format(step_int))

            if normal_flag: # 验证正常格式证明序列
                step_int = len(stmt) + 1 
                correct_flag,stack = self.verify_and_calculate_proof_step_normal(f_hyps,e_hyps,tok,stacks[step_int-1],step_int)  #验证并更新栈状态
                if len(stacks) <= step_int:
                    stacks.append(stack.copy())
                    # print('stacks',stacks)
                else:
                    stacks[step_int] = stack.copy()
                if correct_flag:  # 当前证明步骤若正确 新增步骤
                    stmt.append(tok)  # stmt 索引就是证明步骤序号

            else: # 压缩格式证明序列，要先读到 ） 获取引理，后面接着读到的才是证明序列
                # vprint(30,'compressed proof ###')
                if not end_flag:
                    stmt.append(tok)
                if tok == ')': # 若正好读完引理部分
                    end_flag = True
                    idx_bloc = stmt.index(')') # index of end of label bloc
                    plabels += stmt[1:idx_bloc] # labels which will be referenced later
                    # compressed_proof = ''.join(toks[idx_bloc + 1:])
                    vprint(5, 'Referenced labels:', plabels)
                    label_end = len(plabels)
                    vprint(5, 'Number of referenced labels:', label_end)
                    print('Read Reference Finish!')

                elif end_flag:  # 若读完引理，调用读取+验证证明序列函数
                    step_int = len(stmt) - idx_bloc
                    correct_flag,stack = self.verify_proof_step_compress(f_hyps,e_hyps,conclusion,tok,
                                                            saved_stmts,n_saved_stmts,label_end,
                                                            plabels,stacks[step_int-1],step_int) # 压缩格式
                    # normal_proof = self.transform_from_compress_to_normal(tok,saved_stmts,n_saved_stmts,label_end,plabels,stack)
                    # vprint(30,'normal proof:',normal_proof)
                    if len(stacks) <= step_int :
                        stacks.append(stack.copy())
                    # print('stacks',stacks)
                    else:
                        stacks[step_int] = stack.copy()
                    if correct_flag:  # 当前证明步骤若正确 新增步骤
                        stmt.append(tok)  # stmt 索引就是证明步骤序号
            
            # vprint(20, 'Current Statement:', stmt)  ######
            tok = toks.readc()   ##下一个token

        if not tok:  # 证明序列读取结束
            self.handle_error("Unclosed {}-statement at end of file.".format(stmttype))
            # raise MMError(
            #     "Unclosed {}-statement at end of file.".format(stmttype))
        assert tok == end_token

        vprint(20, 'Statement:', stmt)  
        vprint(10, 'Stack at end of proof:', stack)
        if not stack:
            self.handle_error("Empty stack at end of proof.")
            # raise MMError(
            #     "Empty stack at end of proof.")
        if len(stack) > 1:
            self.handle_error(
                "Stack has more than one entry at end of proof (top " +
                "entry: {} ; proved assertion: {}).".format(
                    stack[0],
                    conclusion))
            # raise MMError(
            #     "Stack has more than one entry at end of proof (top " +
            #     "entry: {} ; proved assertion: {}).".format(
            #         stack[0],
            #         conclusion))
        if stack[0] != conclusion: #最后栈中元素和结论不相同
            self.handle_error(("Stack entry {} does not match proved " +
                        " assertion {}.").format(stack[0], conclusion))
            # raise MMError(("Stack entry {} does not match proved " +
            #             " assertion {}.").format(stack[0], conclusion))
        else:
            vprint(3, 'Correct proof!')
        self.update_backup()
        
        

    def verify_and_calculate_proof_step_normal(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            label: str,
            stack: list[Stmt],
            step_int: int) -> tuple[bool,list[Stmt]]:
        """对normal格式的证明序列 单个或多个步骤进行验证; 返回 当前步骤是否错误 & 新的栈状态
        """
        correct_flag = True
        # vprint(30,'verify_and_calculate_proof_step_normal(f_hyps,e_hyps,tok,stack,step_int)',f_hyps,e_hyps,label,stack,step_int)
        active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        # vprint(30,'Step:',step_int,' label:', label) 
        # print('self:',self)
        # print('active_hypotheses',active_hypotheses)
        if step_int == 0:
            self.roll_back(False)
        # print('now active_hypotheses:===',active_hypotheses)
        stmt_info = self.labels.get(label)  
        if stmt_info:     
            label_type = stmt_info[0] 
            if label_type in {'$e', '$f'}:
                if label in active_hypotheses:
                    try:
                        self.treat_step(stmt_info, stack)
                    except:
                        correct_flag = False
                    self.update_backup()
                else:
                    if step_int == 0:
                        pass
                    else:
                        self.handle_error(f"The label {label} is the label of a nonactive hypothesis.")
                        correct_flag = False
                    # raise MMError(f"The label {label} is the label of a nonactive hypothesis.")
            else:
                try:
                    self.treat_step(stmt_info, stack)
                except:
                    correct_flag = False
                self.update_backup()
        else:
            if step_int == 0:
                pass
            else:
                self.handle_error(f"No statement information found for label {label}")
                correct_flag = False
        return correct_flag,stack

    def verify_proof_step_compress(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            tok: str,      #单个证明步骤或多个
            saved_stmts: list,
            n_saved_stmts: int,
            label_end: int,
            plabels: list[Label | None],
            stack: list[Stmt],
            step_int: int) -> tuple[bool,list[Stmt]]:
        """对compressed格式的证明序列 单个或多个步骤进行验证"""
        vprint(30,'verify_proof_step_compres(f_hyps,e_hyps,conclusion,tok,saved_stmts,n_saved_stmts, label_end,plabels,stack):',f_hyps,e_hyps,conclusion,tok,saved_stmts,n_saved_stmts, label_end,plabels,stack)
        toks = list(tok)    
        cur_int = 0 
        correct_flag = True

        for ch in toks:
            if ch == 'Z':
                proof_int = -1
            elif 'A' <= ch <= 'T':
                # proof_ints.append(20 * cur_int + ord(tok) - 65)  # ord('A') = 65
                proof_int = 20 * cur_int + ord(ch) - 65  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85                    
            vprint(21,'Step_int:',step_int,' proof_int :', proof_int) ###  以上，得到proof_int
            
            if proof_int == -1:  # save the current step for later reuse
                stmt = stack[-1]
                vprint(15, 'Saving step', stmt)
                saved_stmts.append(stmt)
                n_saved_stmts += 1
            elif proof_int < label_end:
                # proof_int denotes an implicit hypothesis or a label in the
                # label bloc
                # print('treat_step(self,step: FullStmt,stack: list[Stmt]):',self.labels[plabels[proof_int] or ''], stack)
                try:
                    self.treat_step(self.labels[plabels[proof_int] or ''], stack)
                except:
                    correct_flag = False

            elif proof_int >= label_end + n_saved_stmts:
                self.handle_error(
                    ("Not enough saved proof steps ({} saved but calling " +
                        "the {}th).").format(
                         n_saved_stmts,
                         proof_int))
                # MMError(
                #     ("Not enough saved proof steps ({} saved but calling " +
                #         "the {}th).").format(
                #          n_saved_stmts,
                #          proof_int))
                correct_flag = False
            else:  # label_end <= proof_int < label_end + n_saved_stmts
                # proof_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                stmt = saved_stmts[proof_int - label_end]
                vprint(15, 'Reusing step', stmt)
                try:
                    self.treat_step(
                        ('$a',
                            (set(), [], [], stmt)),
                            stack)
                except:
                    correct_flag = False
            
            if correct_flag:
                self.update_backup()
        return correct_flag,stack

    def read_non_p_stmt(self, stmttype: Stmttype, toks: Toks) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        non-$p-statement) and return the list of tokens until the next
        end-statement token '$.'.
        """
        return self.readstmt_aux(stmttype, toks, end_token="$.")

    def read_p_stmt(self, toks: Toks) -> tuple[Stmt, Stmt]:
        """Read tokens from the input (assumed to be at the beginning of a
        p-statement) and return the couple of lists of tokens (stmt, proof)
        appearing in "$p stmt $= proof $.".
        """

        stmt = self.readstmt_aux("$p", toks, end_token="$=")
        proof = self.readstmt_aux("$=", toks, end_token="$.")   # 读取证明序列(Stmt类型)
        # print('proof stmt:',proof)
        return stmt, proof

    def read(self, toks: Toks, current_proof: Stmt = None
             , full_flag: bool = True, only_calculate: bool = False
             ) -> tuple[list[Fhyp],list[Ehyp]]:  
        """Read the given token list to update the database and verify its
        proofs.
        若参数current_proof不为空, 即用户另外传入当前更新的证明序列, 则读到$p时只读定理, 不读$= ... $.
        参数 full_flag 默认为 True,若为 False, 表示当前传入的不是完整的证明序列

        only_calculate:默认False,若为True,只对证明序列进行栈操作，不验证证明结果
        """
        self.fs.push() #向framestack 入栈一个空的 frame
        label = None
        # print(">>", end=' ')
        tok = toks.readc()
        while tok and tok != '$}':
            # vprint(30,'tok:',tok) #

            if tok == '$c':
                for tok in self.read_non_p_stmt(tok, toks):
                    flag = self.add_c(tok)
                    if not flag:
                        break

            elif tok == '$v':
                for tok in self.read_non_p_stmt(tok, toks):
                    flag = self.add_v(tok)
                    if not flag:
                        break

            elif tok == '$f':
                stmt = self.read_non_p_stmt(tok, toks)
                flag = True
                if not label:
                    self.handle_error(
                        '$f must have label (statement: {})'.format(stmt))
                    flag = False

                if len(stmt) != 2:
                    self.handle_error(
                        '$f must have length two but is {}'.format(stmt))
                    flag = False

                if flag:
                    self.add_f(stmt[0], stmt[1], label)
                    self.labels[label] = ('$f', [stmt[0], stmt[1]])
                    self.update_backup()
                    label = None

            elif tok == '$e':
                if not label:
                    self.handle_error('$e must have label')

                else:
                    stmt = self.read_non_p_stmt(tok, toks)
                    self.fs.add_e(stmt, label)
                    self.labels[label] = ('$e', stmt)
                    self.update_backup()
                    label = None

            elif tok == '$a':
                if not label:
                    self.handle_error('$a must have label')

                else:
                    self.labels[label] = (
                        '$a', self.fs.make_assertion(
                            self.read_non_p_stmt(tok, toks)))
                    self.update_backup()
                    label = None

            elif tok == '$p': # 读可证明的定理
                vprint(2,'read $p:',tok)   ######
                if not label:
                    self.handle_error('$p must have label')

                else:
                    try:
                        if only_calculate: #只计算栈结果，不验证完整序列 (不知道要证明的最终断言 conclusion)
                            empty = self.readstmt_aux("$p", toks, end_token="$=") 
                            # 获取dvs, f_hyps, e_hyps,
                            dvs, f_hyps, e_hyps = self.fs.get_hyps()
                            print('current====dvs, f_hyps, e_hyps:',dvs, f_hyps, e_hyps)
                            if self.verify_proofs:
                                vprint(2, 'Calculate:', label)
                                self.read_proof_and_calculate("$=", toks, f_hyps, e_hyps, end_token="$.")
                            # 现在得到的 f_hyps, e_hyps是否正确   conclusion最后怎么获取
                            # 先定义conclusion为空
                            conclusion = []
                            self.labels[label] = ('$p', (dvs, f_hyps, e_hyps, conclusion))
                            self.update_backup()
                           
                        else:
                            # stmt, proof = self.read_p_stmt(toks)  # 读取文件中的定理和证明序列
                            stmt = self.readstmt_aux("$p", toks, end_token="$=")  #读取文件中的定理
                            dvs, f_hyps, e_hyps, conclusion = self.fs.make_assertion(stmt) #要证明的assersion
                        
                            if self.verify_proofs:
                                vprint(2, 'Verify:', label)
                                if current_proof == None:
                                    self.read_proof_and_verify("$=", toks, f_hyps, e_hyps, conclusion, end_token="$.")
                                    # self.verify(f_hyps, e_hyps, conclusion, proof,full_flag)

                                else: #有传入当前更新的证明序列,
                                    vprint(20, 'Statement:', current_proof)
                                    # print('self.verify(f_hyps, e_hyps, conclusion, current_proof):',f_hyps, e_hyps, conclusion, current_proof)
                                    self.verify(f_hyps, e_hyps, conclusion, current_proof,full_flag)  # 对当前传入的证明序列进行验证

                            self.labels[label] = ('$p', (dvs, f_hyps, e_hyps, conclusion))
                        self.update_backup()
                        label = None
                    except:
                        self.handle_error("Error")
                        self.roll_back()
            elif tok == '$d': # 似乎没有异常处理?
                self.fs.add_d(self.read_non_p_stmt(tok, toks))

            elif tok == '${':
                self.read(toks)

            elif tok == '$)':
                self.handle_error("Unexpected '$)' while not within a comment")

            elif tok[0] != '$':
                if tok in self.labels:
                    self.handle_error("Label {} multiply defined.".format(tok))

                else:
                    label = tok
                    vprint(20, 'Label:', label)

                    if label == self.stop_label:
                        # TODO: exit gracefully the nested calls to self.read()
                        sys.exit(0)

                    if label == self.begin_label:
                        self.verify_proofs = True
                        self.update_backup()

            else:
                self.handle_error("Unknown token: '{}'.".format(tok))

            # print(">>", end=' ')
            tok = toks.readc()
        self.fs.pop()
        return f_hyps,e_hyps

    def treat_step(self,
                   step: FullStmt,
                   stack: list[Stmt]) -> None:
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        # vprint(10, 'Proof step:', step)
        if is_hypothesis(step):
            _steptype, stmt = step
            stack.append(stmt)
        elif is_assertion(step):
            _steptype, assertion = step
            dvs0, f_hyps0, e_hyps0, conclusion0 = assertion
            npop = len(f_hyps0) + len(e_hyps0)
            sp = len(stack) - npop
            if sp < 0:
                # self.handle_error(
                #     ("Stack underflow: proof step {} requires too many " +
                #      "({}) hypotheses.").format(
                #         step,
                #         npop))
                raise MMError(
                    ("Stack underflow: proof step {} requires too many " +
                     "({}) hypotheses.").format(
                        step,
                        npop))
            subst: dict[Var, Stmt] = {}
            for typecode, var in f_hyps0:
                entry = stack[sp]
                if entry[0] != typecode:
                    # self.handle_error(
                    #     ("Proof stack entry {} does not match floating " +
                    #      "hypothesis ({}, {}).").format(entry, typecode, var))
                    raise MMError(
                        ("Proof stack entry {} does not match floating " +
                         "hypothesis ({}, {}).").format(entry, typecode, var))
                subst[var] = entry[1:]
                sp += 1
            # vprint(15, 'Substitution to apply:', subst)
            for h in e_hyps0:
                entry = stack[sp]
                subst_h = apply_subst(h, subst)
                if entry != subst_h:
                    # self.handle_error(("Proof stack entry {} does not match " +
                    #                "essential hypothesis {}.")
                    #               .format(entry, subst_h))
                    raise MMError(("Proof stack entry {} does not match " +
                                   "essential hypothesis {}.")
                                  .format(entry, subst_h))
                sp += 1
            for x, y in dvs0:
                vprint(16, 'dist', x, y, subst[x], subst[y])
                x_vars = self.fs.find_vars(subst[x])
                y_vars = self.fs.find_vars(subst[y])
                vprint(16, 'V(x) =', x_vars)
                vprint(16, 'V(y) =', y_vars)
                for x0, y0 in itertools.product(x_vars, y_vars):
                    if x0 == y0 or not self.fs.lookup_d(x0, y0):
                        # self.handle_error("Disjoint variable violation: " +
                        #               "{} , {}".format(x0, y0))
                        raise MMError("Disjoint variable violation: " +
                                      "{} , {}".format(x0, y0))
            del stack[len(stack) - npop:]
            stack.append(apply_subst(conclusion0, subst))
        self.update_backup()
        # vprint(12, 'Proof stack:', stack)
        # print('Proof stack:', stack)

    def treat_normal_proof(self, proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given normal proof has been
        processed.

        """
        vprint(30,'[treat_normal_proof(proof)]:',proof) 
        stack: list[Stmt] = []
        active_hypotheses = {label for frame in self.fs for labels in (frame.f_labels, frame.e_labels) for label in labels.values()}
        for label in proof:
            vprint(30,'label in proof:', label) 
            stmt_info = self.labels.get(label)
            if stmt_info:
                label_type = stmt_info[0]
                if label_type in {'$e', '$f'}:
                    if label in active_hypotheses:
                        self.treat_step(stmt_info, stack)
                    else:
                        raise MMError(f"The label {label} is the label of a nonactive hypothesis.")
                else:
                    self.treat_step(stmt_info, stack)
            else:
                raise MMError(f"No statement information found for label {label}")
        return stack
    
    def treat_compressed_proof(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given compressed proof for an
        assertion with the given $f and $e-hypotheses has been processed.
        """
        # Preprocessing and building the lists of proof_ints and labels
        vprint(30,'[treat_compressed_proof(f_hyps, e_hyps, proof)]:',f_hyps, e_hyps, proof) 
        print('[treat_compressed_proof(f_hyps, e_hyps, proof)]:',f_hyps, e_hyps, proof)
        flabels = [self.fs.lookup_f(v) for _, v in f_hyps]
        elabels = [self.fs.lookup_e(s) for s in e_hyps]
        plabels = flabels + elabels  # labels of implicit hypotheses
        idx_bloc = proof.index(')')  # index of end of label bloc
        plabels += proof[1:idx_bloc]  # labels which will be referenced later
        compressed_proof = ''.join(proof[idx_bloc + 1:])
        print('Compressed proof steps:', compressed_proof)
        
        vprint(5, 'Referenced labels:', plabels)
        label_end = len(plabels)
        vprint(5, 'Number of referenced labels:', label_end)
        vprint(5, 'Compressed proof steps:', compressed_proof)
        vprint(5, 'Number of steps:', len(compressed_proof))
        proof_ints = []  # integers referencing the labels in 'labels'
        cur_int = 0  # counter for radix conversion
        for ch in compressed_proof:
            if ch == 'Z':
                proof_ints.append(-1)
            elif 'A' <= ch <= 'T':
                proof_ints.append(20 * cur_int + ord(ch) - 65)  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85
        vprint(5, 'Integer-coded steps:', proof_ints)
        # Processing of the proof
        stack: list[Stmt] = []  # proof stack
        # statements saved for later reuse (marked with a 'Z')
        saved_stmts = []
        # can be recovered as len(saved_stmts) but less efficient
        n_saved_stmts = 0
        for proof_int in proof_ints:
            vprint(21,'proof_int in proof_ints:', proof_int) ###
            if proof_int == -1:  # save the current step for later reuse
                stmt = stack[-1]
                vprint(15, 'Saving step', stmt)
                saved_stmts.append(stmt)
                n_saved_stmts += 1
            elif proof_int < label_end:
                # proof_int denotes an implicit hypothesis or a label in the
                # label bloc
                self.treat_step(self.labels[plabels[proof_int] or ''], stack)
            elif proof_int >= label_end + n_saved_stmts:
                MMError(
                    ("Not enough saved proof steps ({} saved but calling " +
                    "the {}th).").format(
                        n_saved_stmts,
                        proof_int))
            else:  # label_end <= proof_int < label_end + n_saved_stmts
                # proof_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                stmt = saved_stmts[proof_int - label_end]
                vprint(15, 'Reusing step', stmt)
                self.treat_step(
                    ('$a',
                     (set(), [], [], stmt)),
                    stack)
        return stack

    def verify(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            proof: list[str],
            full_flag: bool = True) -> None:
        """Verify that the given proof (in normal or compressed format) is a
        correct proof of the given assertion.

        参数 full_flag 默认为 True,若为 False, 表示当前传入的不是完整的证明序列
        """
        # It would not be useful to also pass the list of dv conditions of the
        # assertion as an argument since other dv conditions corresponding to
        # dummy variables should be 'lookup_d'ed anyway.
        vprint(30,'[verify(f_hyps, e_hyps, conclusion, proof)]:',f_hyps, e_hyps, conclusion, proof)

        if proof[0] == '(':  # compressed format
            stack = self.treat_compressed_proof(f_hyps, e_hyps, proof)
        else:  # normal format
            stack = self.treat_normal_proof(proof)

        if full_flag:  # 已完成证明(是完整证明序列)
            vprint(10, 'Stack at end of proof:', stack)
            if not stack:
                raise MMError(
                    "Empty stack at end of proof.")
            if len(stack) > 1:
                raise MMError(
                    "Stack has more than one entry at end of proof (top " +
                    "entry: {} ; proved assertion: {}).".format(
                        stack[0],
                        conclusion))
            if stack[0] != conclusion: #最后栈中元素和结论不相同
                raise MMError(("Stack entry {} does not match proved " +
                            " assertion {}.").format(stack[0], conclusion))
            vprint(3, 'Correct proof!')

        else: # 未完成证明(证明序列不完整)
            vprint(10, 'Stack state of current proof steps:', stack)
            if len(stack) == 1 and stack[0] == conclusion: # 当前栈中只有一个元素,且和结论相同,可以视为完整证明
                vprint(3, 'Correct proof!')


    def __str__(self):
        return f"MM(constants={self.constants}, fs={[str(f) for f in self.fs]}, labels={self.labels}, " \
               f"begin_label={self.begin_label}, stop_label={self.stop_label}, " \
               f"verify_proofs={self.verify_proofs})"

    def dump(self) -> None:
        """Print the labels of the database."""
        print(self.labels)


    def transform_from_compress_to_normal(
            self,
            tok: str,      #单个证明步骤或多个
            saved_stmts: list,
            n_saved_stmts: int,
            label_end: int,
            plabels: list[Label | None],
            stack: list[Stmt]) -> list[Stmt]:
        """将压缩格式证明转化为正常格式"""
        vprint(30,'transform_from_compress_to_normal(f_hyps,e_hyps,conclusion,tok,saved_stmts,n_saved_stmts, label_end,plabels,stack):',tok,saved_stmts,n_saved_stmts, label_end,plabels,stack)
        toks = list(tok)    
        cur_int = 0 
        normal_proof = []

        for ch in toks:
            if ch == 'Z':
                proof_int = -1
            elif 'A' <= ch <= 'T':
                # proof_ints.append(20 * cur_int + ord(tok) - 65)  # ord('A') = 65
                proof_int = 20 * cur_int + ord(ch) - 65  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85                    
            vprint(21,' proof_int :', proof_int) ###  以上，得到proof_int
            
            if proof_int == -1:  # save the current step for later reuse
                stmt = stack[-1]
                vprint(15, 'Saving step', stmt)
                saved_stmts.append(stmt)
                n_saved_stmts += 1
            elif proof_int < label_end:
                # normal_proof.append(self.labels[plabels[proof_int]or ''] )
                normal_proof.append(plabels[proof_int])
                
            elif proof_int >= label_end + n_saved_stmts:
                self.handle_error(
                    ("Not enough saved proof steps ({} saved but calling " +
                        "the {}th).").format(
                         n_saved_stmts,
                         proof_int))
                # MMError(
                #     ("Not enough saved proof steps ({} saved but calling " +
                #         "the {}th).").format(
                #          n_saved_stmts,
                #          proof_int))
            else: 
                stmt = saved_stmts[proof_int - label_end]
                vprint(15, 'Reusing step', stmt)
                normal_proof.append(('$a',
                        (set(), [], [], stmt)))            
        return normal_proof

    # def run_in_mcts( ) -> None:
    #     mm = MM(None, None)
    #     mm.read(Toks(db_file),only_calculate=True)   # 证明计算程序 （未知可证明的断言，只有证明序列）


    def calculate_and_verify_metamath(
            self,
            def_database = sys.stdin, 
            def_logfile = sys.stdout, 
            def_verbosity: int = 30, 
            begin_label=None, 
            stop_label=None, 
            def_only_calculate = False
            ) -> tuple[list[Fhyp],list[Ehyp]]:
            """
            使用示例：
            import mmverify
            verbosity = 30
            filename='data/anatomy.mm'
            logfile = 'logs/anatomu0509.log'
            # mm = mmverify.calculate_and_verify_metamath(filename,logfile,verbosity)  #读文件输出写到日志文件
            # mm = mmverify.calculate_and_verify_metamath(filename,def_verbosity=verbosity)  #从控制台输出
            mm = mmverify.calculate_and_verify_metamath()  #控制台输入输出

            若def_only_calculate为True,只计算。 该函数只读到$= 需要再调用函数****读证明步骤
            """
            
            print('def_database,def_logfile,def_verbosity:',def_database,def_logfile,def_verbosity)
            
            global verbosity,logfile,database
            verbosity = def_verbosity

            if def_logfile != sys.stdout:
                logfile = open(def_logfile, "w",encoding='ascii')
            else:
                logfile = def_logfile

            if def_database != sys.stdin:
                database = open(def_database,"r",encoding='ascii')
            else:
                database = def_database


            vprint(1, 'mmverify.py -- Proof verifier for the Metamath language')
            vprint(1, 'Reading source file "{}"...'.format(database.name))

            f_hyps,e_hyps = self.read(Toks(database), only_calculate=def_only_calculate)   # 若only_calculate = True （未知可证明的断言）

            # if def_only_calculate: #若只使用计算功能，读到了$=，需要再一步一步拿到证明步骤
                
            # vprint(1, 'No errors were found.')
            print("READ FINISH")
            return f_hyps,e_hyps


 

if __name__ == '__main__':
    """Parse the arguments and verify the given Metamath database."""
    parser = argparse.ArgumentParser(description="""Verify a Metamath database.
      The grammar of the whole file is verified.  Proofs are verified between
      the statements with labels BEGIN_LABEL (included) and STOP_LABEL (not
      included).

      One can also use bash redirections:
         '$ python3 mmverify.py < file.mm 2> file.log'
      in place of
         '$ python3 mmverify.py file.mm --logfile file.log'
      but this fails in case 'file.mm' contains (directly or not) a recursive
      inclusion statement '$[ file.mm $]'.""")
    parser.add_argument(
        'database',
        nargs='?',
        type=argparse.FileType(
            mode='r',
            encoding='ascii'),
        default=sys.stdin,
        help="""database (Metamath file) to verify, expressed using relative
          path (defaults to <stdin>)""")
    parser.add_argument(
        '-l',
        '--logfile',
        dest='logfile',
        type=argparse.FileType(
            mode='w',
            encoding='ascii'),
        default=sys.stdout,
        help="""file to output logs, expressed using relative path (defaults to
          <stderr>)""")
    parser.add_argument(
        '-v',
        '--verbosity',
        dest='verbosity',
        default=30,
        type=int,
        help='verbosity level (default=0 is mute; higher is more verbose)')
    parser.add_argument(
        '-b',
        '--begin-label',
        dest='begin_label',
        type=str,
        help="""label where to begin verifying proofs (included, if it is a
          provable statement)""")
    parser.add_argument(
        '-s',
        '--stop-label',
        dest='stop_label',
        type=str,
        help='label where to stop verifying proofs (not included)')
    
    parser.add_argument( # 用户传入的证明序列,默认为None
        '-p',
        '--current-proof',
        dest='current_proof',
        default= None,
        # type=Stmt,
        type= str,
        help='Current proof sequence ')

    print('test new!')
    args = parser.parse_args()
    verbosity = args.verbosity
    db_file = args.database
    logfile = args.logfile
    current_proof = args.current_proof
    mm = MM(None,None)
    mm.calculate_and_verify_metamath(db_file, logfile, verbosity, args.begin_label, args.stop_label, current_proof)
    
    
# data/big-unifier.mm  proof: ' ( wi ax-min ax-maj ax-mp ) ABBCFECFFEFFZFZKDFADFFZAFZFJMFFZKNJFFNFZFAOFFZMPAFFZFPFQPFZFLRFFLNKMJAJNQPLAPGPMKBADCEOARLHI'
# data/anatomy.mm  proof: 'ws wr wp w2 w2'


