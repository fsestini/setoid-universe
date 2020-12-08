{-# OPTIONS --without-K --prop #-}

module Readme where

----------------------------------------------------------------------
-- formalisation for the paper "Constructing a universe for the setoid
-- model"
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
import Setoid.IRSets     -- universe of sets constructed by
                         -- induction-recursion closed under Bool, Π,
                         -- Σ, ⊥ and includes propositions
import Setoid.Sets       -- universe of sets constructed by
                         -- induction-induction closed under Bool, Π
import Setoid.SeTT       -- setoid type theory rules for equality type
import Setoid.Id         -- Martin-Löf's identity type (has
                         -- definitional β rule)

import Setoid.Sets.lib   -- the inductive-inductive type (IIT) for the
                         -- universe of sets
import Setoid.Sets2.lib  -- the same IIT, but defined only using
                         -- indexed types, derviation of the simple
                         -- elimination principle

import Abbrevs           -- abbreviations such as vz, vs, wk, _⇒_,
                         -- closure of P under Unit,Π,Σ

import Equations         -- definitional equalities validated by the
                         -- setoid model

----------------------------------------------------------------------
-- not part of the paper
----------------------------------------------------------------------

import Setoid.Sets1.lib  -- different version of the Setoid.Sets2.lib
import Setoid.Sets1      -- partial construction of the universe using
                         -- Sets1.lib
import Setoid.Sets2b.lib -- different version of the Setoid.Sets2.lib


-- the setoid model where Ty Γ is given by a groupoid morphism from
-- the setoid (groupoid) Γ to the groupoid of setoids

import SetoidHom.CwF
import SetoidHom.Pi
import SetoidHom.Bool
import SetoidHom.Sigma
import SetoidHom.Id -- "surface language"
-- import SetoidHom.Sets
import AbbrevsHom
import EquationsHom

-- the setoid model where Π,Σ,⊤ in Props is defined by truncation

import SetoidRed.CwF
import SetoidRed.Pi
-- import SetoidRed.Sigma -- TODO: unsolved metas
import SetoidRed.Unit
import SetoidRed.Bool
import SetoidRed.Props  -- universe of propositions and propositional truncation
import SetoidRed.Sets   -- universe of sets closed under Bool and Π
import SetoidRed.SeTT   -- setoid type theory rules for equality type
-- import SetoidRed.Id     -- Martin-Löf's identity type (has definitional β rule)
                            -- TODO: unsolved metas

-- import AbbrevsRed       -- TODO: unsolved metas
-- import EquationsRed  -- TODO: unsolved metas
