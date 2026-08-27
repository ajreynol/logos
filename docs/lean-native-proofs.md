# Checking Lean-native proofs

The primary input format of Logos is the s-expression (Eunoia) syntax read by `logos` and
described in [parser.md](parser.md).  This document describes a secondary path: proofs
written directly as Lean evaluation scripts, read by the `logos-native` executable.  See
the [README](../README.md) for building the executables.

This path is a development convenience, not the verified entry point.  A `true` from
`logos-native` is weaker than the `correct` that `logos` prints; see
[What a `true` means](#what-a-true-means) below.

`logos-native` reads files containing Lean terms and an evaluation statement:

```bash
lake build logos-native
lake exe logos-native test/regress/test-simple.cpc.lean
```

The input is a file containing an evaluation statement to be read by the Lean parser.
An example of such a file is the following:

```
import Cpc.Logos
open Eo
def t1 : Term := (Term.UConst 1 (Term.UOp UserOp.Int))
def t2 : Term := (Term.UConst 2 (Term.UOp UserOp.Int))
def t3 : Term := (Term.Apply (Term.UOp UserOp.eq) t2)
def t4 : Term := (Term.Apply t3 t1)
def t5 : Term := (Term.Apply (Term.UOp UserOp.eq) t1)
def t6 : Term := (Term.Apply t5 t2)
def t7 : Term := (Term.Apply (Term.UOp UserOp.not) t6)
def s0 : CState := logos_init_state
def s1 : CState := (logos_invoke_assume s0 t4)
def s2 : CState := (logos_invoke_assume s1 t7)
def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.contra CArgList.nil (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
#eval!
(logos_state_is_refutation s4)
```

Proof checking succeeds if executing `logos-native` on one of these files returns `true`.

Logos assumes that scripts define a state that is constructed iteratively starting from
`logos_init_state`, followed by a sequence of `logos_invoke_assume` commands (the assumptions of the proof),
followed by a sequence of `logos_invoke_cmd` commands.
A state is a refutation if the last proven formula was `false` and if
all assumptions introduced via `assume_push` commands are closed by corresponding `step_pop` commands.
The semantics of these commands mimics the Eunoia logical framework;
for details see https://github.com/cvc5/ethos/blob/main/user_manual.md.

The examples in `test/regress/*.cpc.lean` are in this format; CI runs each of them through
`logos-native` and requires the output `true`.

## What a `true` means

`logos-native` elaborates the file as Lean and reports the value of its `#eval!`, so a
`true` says that this script evaluates to `true`.  Nothing checks that the script has the
shape described above — that is why the paragraph above says Logos *assumes* it.

Even for a script that does have that shape, a `true` is not the conclusion of
`correct___logos_check_proof`, which is stated about `logos` and the text of an
s-expression proof file (see [Correctness](../README.md#correctness)).  Two things the
`logos` path does are missing here:

* `logos_state_is_refutation` is `__eo_state_is_refutation`, the checker run alone.  The
  two translation side conditions of `correct___eo_is_refutation` are never evaluated, so
  the `incomplete` verdict has no counterpart: a script mentioning terms the SMT-LIB
  specification does not model still returns `true`.
* `logos_invoke_assume` pushes an input assumption with no well-formedness guard, where
  `logos` pushes one only if it is Boolean-typed and closed
  (`logos_invoke_input_assume`, `Cpc/Api.lean`).  That guard is what the soundness proof
  needs.
