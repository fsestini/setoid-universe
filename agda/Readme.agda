{-# OPTIONS --without-K --prop --rewriting #-}

module Readme where

----------------------------------------------------------------------
-- formalisation originally distributed for the paper
-- "Constructing a universe for the setoid model"
----------------------------------------------------------------------

-- import con-ty-example -- Example of reduction of a finitary
                         -- inductive-inductive type to inductive families.

import lib               -- library (only defining _≡_ for now)

-- the private definitions for the setoid model: Setoid.lib,
-- SetoidHom.lib, SetoidRed.lib

-- parts of the setoid model (these use Setoid.lib)

import Setoid.CwF
import Setoid.Pi
import Setoid.Sigma
import Setoid.Empty
import Setoid.Unit
import Setoid.Bool
import Setoid.Props      -- universe of propositions and propositional
                         -- truncation
import Setoid.SetsIR     -- universe of sets constructed by
                         -- induction-recursion closed under Bool, Π,
                         -- Σ, ⊥ and includes propositions
import Setoid.SetsII     -- universe of sets constructed by
                         -- induction-induction closed under Bool, Π
import Setoid.Sets       -- universe of sets constructed by inductive
                         -- families and strong transport
import Setoid.SeTT       -- setoid type theory rules for equality type
import Setoid.Id         -- Martin-Löf's identity type (has
                         -- definitional β rule)

import Setoid.SetsII.lib -- the inductive-inductive type (IIT) for the
                         -- universe of sets
import Setoid.Sets.lib   -- the same IIT, but defined only using
                         -- inductive families, derviation of the
                         -- simple elimination principle

import Abbrevs           -- abbreviations such as vz, vs, wk, _⇒_,
                         -- closure of P under Unit,Π,Σ

import Equations         -- definitional equalities validated by the
                         -- setoid model

----------------------------------------------------------------------
-- additional formalisation for the PhD thesis
-- "Bootstrapping Extensionality"
----------------------------------------------------------------------

import Setoid.Sets.gen-elim     -- encoding of the general eliminators for
                                -- the universe IIT with definitional β-equations
import Setoid.UnivElim-SetsII   -- Universe eliminator/typecase for the universe
                                -- defined in Setoid.SetsII, i.e. the
                                -- inductive-inductive universe.

import Setoid.Sets3.mini-univ   -- mini IR universe to support the new universe IIT
import Setoid.Sets3.encoding    -- encoding of the universe IIT (types, constructors)
                                -- using inductive families
import Setoid.Sets3.gen-elim    -- encoding of the general eliminators for the IIT
                                -- with definitional β-equations

import Setoid.Sets3.lib-abbrev       -- compact redefinition of the IIT using records
import Setoid.Sets3.encoding-abbrev  -- encoding of the compact IIT
                                     -- in terms of the one from Setoid.Sets3.encoding
import Setoid.Sets3             -- The setoid universe using the new IIT
                                -- (as defined Setoid.Sets3.lib-abbrev)
import Setoid.UnivElim-Sets3    -- Universe eliminator/typecase for the universe
                                -- defined in Setoid.Sets3

import Setoid.SetsII-from-Sets3 -- definition of SetsII in terms of Sets3 and its
                                -- induction principle
