#!/usr/bin/env python3

"""
Run this script from one folder up with

    $ python3 -m sublime-coq.test

This script requires the Nix package manger (https://nixos.org/nix/).  It uses
Nix to wrangle multiple versions of Coq to test the plugin's version
compatibility.
"""

import subprocess

if False:

    args = ["cat", "-u"]

    if True:

        proc = subprocess.Popen(args, bufsize=0, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        proc.stdin.write("hello".encode("ascii"));
        proc.stdin.flush()

        print(proc.stdout.read(1024))

        proc.stdin.close()
        print(proc.wait())

    else:

        proc = subprocess.Popen(args, stdin=subprocess.PIPE)
        proc.stdin.write("hello".encode("ascii"));
        proc.stdin.flush()

        proc.stdin.close()
        print(proc.wait())

def test_xml_muncher():

    from . import util

    cases = ["  <val x='b<>'> <hi/> hello </val><bool/> ", "<bool/>"]

    muncher = util.XMLMuncher()

    for xml in cases:
        print("testing {}".format(repr(xml)))
        muncher.reset()

        for c in xml:
            for tag in muncher.process(c):
                print(" -> '{}'".format(tag))

def path_to_coqtop(version):
    nix = subprocess.Popen(
        ["nix-build", "--no-out-link", "<nixpkgs>", "-A", "coq_{}_{}".format(*version)],
        stdout=subprocess.PIPE)
    for line in nix.stdout:
        print(line)
        last = line
    ret = nix.wait()
    if ret != 0:
        raise Exception()
    return last.decode("ascii").strip()

COQ_VERSIONS = [
    (8,9),
    (8,8),
    (8,7),
    (8,6),
    (8,5),
]

if __name__ == "__main__":
    test_xml_muncher()

    from . import coq

    assert coq.find_first_coq_command('(*Require Import Analytical.Analytics.*)\n\nGoal ~ forall a b, a /\\ b.')
    assert coq.find_first_coq_command('\n\nRecord EpsilonLogic := mkLogic {\n\n  Value : Type;\n\n  (* I\'d rather not require this, but it sure makes proofs easier! *)\n  value_eq_dec : forall (v1 v2 : Value), { v1 = v2 } + { v1 <> v2 };\n\n  eval : (Identifier -> Value) -> Term -> Value;\n\n  (* basics: variables & constants *)\n  evalVar : forall env id, eval env (Var id) = env id;\n  evalIntConst : forall env1 env2 i, eval env1 (Int i) = eval env2 (Int i);\n  evalIntInj : forall env i j, i <> j -> eval env (Int i) <> eval env (Int j);\n  evalBoolConst : forall env1 env2 b, eval env1 (Bool b) = eval env2 (Bool b);\n  evalBoolInj : forall env, eval env (Bool true) <> eval env (Bool false);\n  evalIn : forall env x S, eval env (In x S) = eval env (Bool true) \\/ eval env (In x S) = eval env (Bool false);\n  evalInBools : forall env b S, eval env S = eval env Bools ->\n    (eval env (In b S) = eval env (Bool true)) <->\n    (exists b, eval env b = eval env (Bool b));\n  evalInBools : forall env b S, eval env S = eval env Ints ->\n    (eval env (In b S) = eval env (Bool true)) <->\n    (exists i, eval env b = eval env (Int i));\n\n  (* equality *)\n  evalEqTrue : forall env a b, (eval env a = eval env b) <-> (eval env (Eq a b) = eval env (Bool true));\n  evalEqFalse : forall env a b, (eval env a <> eval env b) <-> (eval env (Eq a b) = eval env (Bool false));\n\n  (* if-then-else *)\n  evalIfTrue : forall env cond a b,\n    eval env cond = eval env (Bool true) ->\n    eval env (If cond a b) = eval env a;\n  evalIfFalse : forall env cond a b,\n    eval env cond = eval env (Bool false) ->\n    eval env (If cond a b) = eval env b;\n\n  (* other boolean operations are defined in terms of if-then-else *)\n  evalAnd : forall env a b,\n    eval env (And a b) = eval env (If a b (Bool false));\n  evalOr : forall env a b,\n    eval env (Or a b) = eval env (If a (Bool true) b);\n  evalNot : forall env a,\n    eval env (Not a) = eval env (If a (Bool false) (Bool true));\n\n  (* arithmetic *)\n  evalPlus : forall env iE jE i j,\n    eval env iE = eval env (Int i) ->\n    eval env jE = eval env (Int j) ->\n    eval env (Plus iE jE) = eval env (Int (i + j));\n  evalMinus : forall env iE jE i j,\n    eval env iE = eval env (Int i) ->\n    eval env jE = eval env (Int j) ->\n    eval env (Minus iE jE) = eval env (Int (i - j));\n  evalTimes : forall env iE jE i j,\n    eval env iE = eval env (Int i) ->\n    eval env jE = eval env (Int j) ->\n    eval env (Times iE jE) = eval env (Int (i * j));\n\n  (* Core definition of the "choose" or "epsilon" operator.  If there exists\n   * an x satisfying P(x), then `Choose x | P` returns some x satisfying P. *)\n  evalChoose :\n    forall env x P,\n      (exists value, eval (extendEnv env x value) P = eval env (Bool true)) ->\n      eval (extendEnv env x (eval env (Choose x P))) P = eval env (Bool true);\n\n  (* The second half of the definition of "choose": choose is deterministic.\n   * The syntax of P should not affect the result of `Choose x | P`. *)\n  evalChooseDet :\n    forall env x P Q,\n      ((eval env P = eval env (Bool true)) <-> (eval env Q = eval env (Bool true))) ->\n      eval env (Choose x P) = eval env (Choose x Q)\n\n}.')

    for version in COQ_VERSIONS:
        print("=" * 40 + " COQ VERSION: {}.{}".format(*version))
        path = path_to_coqtop(version)
        proc = coq.CoqBot(
            coq_install_dir=path,
            coq_version=version,
            extra_args=["-q"]) # -q: do not load rcfile
        try:
            i = 0
            text = """
                Record R := { field : nat }.
                Definition x := Build_R 0.
                Definition y := x.(field).
            """
            steps = 0
            while True:
                sent = proc.append(text, start=i)
                if sent:
                    steps += 1
                    i = sent
                else:
                    break
            assert steps == 3, "tokenization gave us {} steps instead of 3".format(steps)

            proc.append("Theorem foo : False \\/ True.")
            proc.append("Proof.")
            print(proc.current_goal())
            proc.append(" - intuition.")
            print(proc.current_goal())
            proc.rewind_to(len(text) + 35)
            proc.append("   right.")
            proc.append("   constructor.")
            print(proc.current_goal())
            proc.append("Qed.")
            print(proc.current_goal())
        finally:
            proc.stop()
