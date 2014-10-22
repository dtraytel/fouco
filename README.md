This repository contains supplementary material related to the paper

    Foundational Extensible Corecursion
    Jasmin Christian Blanchette, Andrei Popescu, and Dmitriy Traytel

The archive corec.tgz provides the Isabelle formalization of the

  1. examples from Section 2 and Hinze and James [28]
  2. metatheory from Section 3
  3. prototype package from Section 4

The formalization has been processed with Isabelle2014 which is available here:

    http://isabelle.in.tum.de/website-Isabelle2014

**1. Examples**

All definitions and proofs from Section 2 as well as all examples from Hinze and
James [28] have been formalized and can be browsed in both pdf
(stream_examples.pdf, tree_examples.pdf, and ufp_examples.pdf) and html
(html/Corec/index.html) formats. The raw Isabelle sources which were used to
generate this pdf and html output are contained in the src/Stream_User and
src/Tree_User folders.

To ease the experimentation we also provide a Haskell file (Examples.hs)
containing all examples (operating on plain Haskell lists rather than streams).

**2. Metatheory**

The metatheory from Section 3 has been formalized for an arbitrary axiomatized
functor F (more precisely bounded natural functor). Only html
(html/Corec/index.html) is available for browsing the formalization here. The
raw Isabelle sources which were used to generate this html output are contained
in the src/Metatheory folder.

**3. Prototype package**

The rudimentary automation that we sketch in Section 4 consists of two shell
scripts

    src/Metatheory/corecupto_init.sh <name> <editor>
    src/Metatheory/corecupto_step.sh <name> <editor>

which are used to initialize the corecursion state and to make a step
(i.e. register a new well-behaved operation) based on the previous corecursion
state, respectively. The scripts copy the metatheory theories to the folder
<name>, rename the theory files and constants in the files according to the
current step number and open the files that the user is supposed to adjust
(replacing the axiomatization with the concrete functor/operation of interest)
with the given <editor>.

The scripts were used to register the example functions on streams and trees as
well-behaved. The output of the scripts can be found in src/Stream and src/Tree;
where only the theory files with "Input" in their names have been further edited
manually. This output was itself used to define the examples from Section 2.
