#!/usr/bin/env python3

"""
Run this script from one folder up with

    $ python3 -m sublime-coq-plugin.test

This script requires the Nix package manger (https://nixos.org/nix/).  It uses
Nix to wrangle multiple versions of Coq to test the plugin's version
compatibility.
"""

import subprocess

from . import util
from . import coq

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

    cases = [
        "  <val x='b&lt;&gt;'> <hi/> hello </val><bool/> ",
        "<bool/>",
        "<foo>&nbsp;</foo>",
    ]

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
    (8,14),
    (8,13),
    (8,12),
    (8,11),
    (8,10),
    (8,9),
    (8,8),
    (8,7),
    (8,6),
    (8,5),
]

def send_all(coq, text):
    """Returns (list_of_commands, end_index)"""
    sent_cmds = []
    i = 0
    while True:
        offset = coq.append(text, start=i)
        if offset:
            sent_cmds.append(text[i:offset])
            i = offset
        else:
            break
    return (sent_cmds, i)

def test_error(path, version):
    proc = coq.CoqBot(
        coq_install_dir=path,
        coq_version=version,
        extra_args=["-q"], # -q: do not load rcfile
        verbose=True)
    try:
        proc.append("Theorem foo : True /\\ True.")
        proc.append("Proof.")
        proc.append("  split.")
        send_all(proc, "  - constructor.")

        try:
            send_all(proc, "  + constructor.")
            assert False, "expected CoqException"
        except coq.CoqException:
            return

    except Exception as e:
        print("!!! CAUGHT {}".format(repr(e)))
        raise
    finally:
        proc.stop()

def test1(path, version):
    proc = coq.CoqBot(
        coq_install_dir=path,
        coq_version=version,
        extra_args=["-q"], # -q: do not load rcfile
        verbose=True)
    try:
        text = """
            Record R := { field : nat }.
            Definition x := Build_R 0.
            Definition y := x.(field)."""
        cmds, _ = send_all(proc, text)
        assert len(cmds) == 3, "tokenization gave us {} steps instead of 3".format(len(cmds))

        proc.append("Theorem foo : False \\/ True.")
        proc.append("Proof.")
        print(proc.current_goal())
        cmds, _ = send_all(proc, " - intuition.")
        assert len(cmds) == 2, "tokenization gave us {} steps instead of 2".format(len(cmds))
        print(proc.current_goal())
        proc.rewind_to(len(text) + 40)
        proc.append("   right.")
        proc.append("   constructor.")
        print(proc.current_goal())
        proc.append("Qed.")
        print(proc.current_goal())

        proc.append('SearchAbout "+".')
        res = proc.current_goal()
        print(res)
        assert "plus_n_O" in res

    finally:
        proc.stop()

TESTS = [
    """
    Require Import Lia.
    Require Import List.
    Import ListNotations.

    Definition nats : list nat := [1; 2; 3; 4].

    (*
    Definition ElemOf {T} (l : list T) : Type :=
      { x : T | In x l }.

    Lemma nats_gtz:
      forall x : ElemOf nats,
        x > 0.
        (* butts *)
    *)

    Notation "'forall' x 'in' l ',' P" :=
      (forall x, In x l -> P)
      (at level 200) : type_scope.

    Lemma nats_gtz:
      forall x in nats,
        x > 0.
    Proof.
      unfold nats.
      intro x.
      simpl.
      intuition lia.
    Qed.
    """
]

def test_trivial_success(path, version):
    for inp in TESTS:
        proc = coq.CoqBot(
            coq_install_dir=path,
            coq_version=version,
            extra_args=["-q"], # -q: do not load rcfile
            verbose=True)
        try:
            send_all(proc, inp)
            print(proc.current_goal())
        finally:
            proc.stop()

def test_retry_after_error(path, version):
    proc = coq.CoqBot(
        coq_install_dir=path,
        coq_version=version,
        extra_args=["-q"], # -q: do not load rcfile
        verbose=True)

    try:
        proc.append("Definition x := 0.")

        try:
            proc.append("Definition y := x = True.")
            assert False, "send should fail"
        except coq.CoqException:
            pass

        proc.append("Definition y := x = 1.")

    finally:
        proc.stop()

if __name__ == "__main__":
    test_xml_muncher()

    assert coq.find_first_coq_command('(*Require Import Analytical.Analytics.*)\n\nGoal ~ forall a b, a /\\ b.')
    assert coq.find_first_coq_command('\n\nRecord EpsilonLogic := mkLogic {\n\n  Value : Type;\n\n  (* I\'d rather not require this, but it sure makes proofs easier! *)\n  value_eq_dec : forall (v1 v2 : Value), { v1 = v2 } + { v1 <> v2 };\n\n  eval : (Identifier -> Value) -> Term -> Value;\n\n  (* basics: variables & constants *)\n  evalVar : forall env id, eval env (Var id) = env id;\n  evalIntConst : forall env1 env2 i, eval env1 (Int i) = eval env2 (Int i);\n  evalIntInj : forall env i j, i <> j -> eval env (Int i) <> eval env (Int j);\n  evalBoolConst : forall env1 env2 b, eval env1 (Bool b) = eval env2 (Bool b);\n  evalBoolInj : forall env, eval env (Bool true) <> eval env (Bool false);\n  evalIn : forall env x S, eval env (In x S) = eval env (Bool true) \\/ eval env (In x S) = eval env (Bool false);\n  evalInBools : forall env b S, eval env S = eval env Bools ->\n    (eval env (In b S) = eval env (Bool true)) <->\n    (exists b, eval env b = eval env (Bool b));\n  evalInBools : forall env b S, eval env S = eval env Ints ->\n    (eval env (In b S) = eval env (Bool true)) <->\n    (exists i, eval env b = eval env (Int i));\n\n  (* equality *)\n  evalEqTrue : forall env a b, (eval env a = eval env b) <-> (eval env (Eq a b) = eval env (Bool true));\n  evalEqFalse : forall env a b, (eval env a <> eval env b) <-> (eval env (Eq a b) = eval env (Bool false));\n\n  (* if-then-else *)\n  evalIfTrue : forall env cond a b,\n    eval env cond = eval env (Bool true) ->\n    eval env (If cond a b) = eval env a;\n  evalIfFalse : forall env cond a b,\n    eval env cond = eval env (Bool false) ->\n    eval env (If cond a b) = eval env b;\n\n  (* other boolean operations are defined in terms of if-then-else *)\n  evalAnd : forall env a b,\n    eval env (And a b) = eval env (If a b (Bool false));\n  evalOr : forall env a b,\n    eval env (Or a b) = eval env (If a (Bool true) b);\n  evalNot : forall env a,\n    eval env (Not a) = eval env (If a (Bool false) (Bool true));\n\n  (* arithmetic *)\n  evalPlus : forall env iE jE i j,\n    eval env iE = eval env (Int i) ->\n    eval env jE = eval env (Int j) ->\n    eval env (Plus iE jE) = eval env (Int (i + j));\n  evalMinus : forall env iE jE i j,\n    eval env iE = eval env (Int i) ->\n    eval env jE = eval env (Int j) ->\n    eval env (Minus iE jE) = eval env (Int (i - j));\n  evalTimes : forall env iE jE i j,\n    eval env iE = eval env (Int i) ->\n    eval env jE = eval env (Int j) ->\n    eval env (Times iE jE) = eval env (Int (i * j));\n\n  (* Core definition of the "choose" or "epsilon" operator.  If there exists\n   * an x satisfying P(x), then `Choose x | P` returns some x satisfying P. *)\n  evalChoose :\n    forall env x P,\n      (exists value, eval (extendEnv env x value) P = eval env (Bool true)) ->\n      eval (extendEnv env x (eval env (Choose x P))) P = eval env (Bool true);\n\n  (* The second half of the definition of "choose": choose is deterministic.\n   * The syntax of P should not affect the result of `Choose x | P`. *)\n  evalChooseDet :\n    forall env x P Q,\n      ((eval env P = eval env (Bool true)) <-> (eval env Q = eval env (Bool true))) ->\n      eval env (Choose x P) = eval env (Choose x Q)\n\n}.')
    assert not coq.find_first_coq_command('Require Import Foo.', end=18)
    assert coq.find_first_coq_command('Require Import Foo.', end=19)
    assert not coq.find_first_coq_command('Require Import Foo.Bar.', end=19)

    charset = "utf-8"
    # this 5-character string has a 3-byte character in the middle
    test_str = b"a \xe2\x89\x88 b".decode(charset)
    assert util.byte_to_character_offset(test_str, 0, charset=charset) == 0
    assert util.byte_to_character_offset(test_str, 1, charset=charset) == 1
    assert util.byte_to_character_offset(test_str, 2, charset=charset) == 2
    assert util.byte_to_character_offset(test_str, 5, charset=charset) == 3
    assert util.byte_to_character_offset(test_str, 6, charset=charset) == 4
    assert util.byte_to_character_offset(test_str, 7, charset=charset) == 5

    for version in COQ_VERSIONS:
        print("=" * 40 + " COQ VERSION: {}.{}".format(*version))
        path = path_to_coqtop(version)

        # test1(path, version)
        test_trivial_success(path, version)
        test_error(path, version)
        test_retry_after_error(path, version)
