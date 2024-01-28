LMFI Coq Project: Micro-compiler
=================================

Marthe : a micro-certified compiler. 
You will find more detailed instructions as comments in the file [`Marthe.v`](Marthe.v) to be completed. It was translated and adapted from a project by Pierre Letouzey.

Useful tactics for the project
------------------------------

- `revert` before using  `induction` to generaliwe as much as possible;
- `eauto` and its variant `eauto using` ; you can also add hints for `eauto` using command `Hint Resolve` ;
- `eapply` useful when applying transitivity lemmas.
