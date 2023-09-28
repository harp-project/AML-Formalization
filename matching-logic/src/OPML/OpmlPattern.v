From Coq Require Import ssreflect ssrfun ssrbool.

From MatchingLogic.OPML Require Import OpmlSignature.

Inductive OPMLPattern {Σ : OPMLSignature} :=
| op_bot (s : opml_sort)
| op_upcast (from to : opml_sort) (φ : OPMLPattern)
.