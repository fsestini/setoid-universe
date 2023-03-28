# setoid-universe

Source code and accompanying Agda formalization for the paper *Constructing a universe for the setoid model*, T. Altenkirch, S. Boulier, A. Kaposi, C. Sattler & F. Sestini, 2021 (link [here](https://doi.org/10.1007%2F978-3-030-71995-1_1))

This repository is forked from the [bitbucket repository](https://bitbucket.org/taltenkirch/setoid-univ) originally linked to the paper. There are additional Agda files not included in the paper or the bitbucket repo, which instead formalize subsequent original content covered by my thesis. These are the following:

* `Setoid/Sets/gen-elim.agda`: implementation of the general eliminators for the universe IIT encoded via inductive families, with definitional β-equations.
* `Setoid/UnivElim-SetsII.agda`: universe eliminator/typecase for the inductive-inductive universe.
* `Setoid/Sets3.agda` and `Setoid/Sets3/*.agda`: alternative formulation of the universe IIT encoded via inductive families. This variant uses mini IR universes for indexing, instead of `Set` and `Prop`. It also supports general eliminators.
* `Setoid/UnivElim-Sets3.agda`: universe eliminator for the `Sets3` variant.
* `Setoid/SetsII-from-Sets3.agda`: implementation of the universe IIT in terms of the alternative encoding `Sets3`. This yields an additional route to encode the universe IIT in terms of inductive families, by going via `Sets3`.

See `agda/Readme.agda` for a full description of the contents of all relevant files in the `agda` folder.
