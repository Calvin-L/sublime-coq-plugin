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

    for version in COQ_VERSIONS:
        print("=" * 40 + " COQ VERSION: {}.{}".format(*version))
        path = path_to_coqtop(version)
        proc = coq.CoqBot(
            coq_install_dir=path,
            coq_version=version,
            extra_args=["-q"]) # -q: do not load rcfile
        try:
            proc.append("Theorem foo : False \\/ True.")
            proc.append("Proof.")
            print(proc.current_goal())
            proc.append(" - intuition.")
            print(proc.current_goal())
            proc.rewind_to(35)
            proc.append("   right.")
            proc.append("   constructor.")
            print(proc.current_goal())
            proc.append("Qed.")
            print(proc.current_goal())
        finally:
            proc.stop()
