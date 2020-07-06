{-# OPTIONS --without-K --prop #-}

module Readme where

-- library (only defining _≡_ for now)

import lib

-- the private definitions for the setoid model

-- we don't import Setoid.lib, SetoidHom.lib, SetoidRed.lib

-- parts of the setoid model (these use Setoid.lib)

import Setoid.CwF
import Setoid.Pi
import Setoid.Sigma
import Setoid.Empty
import Setoid.Unit
import Setoid.Bool
import Setoid.Props      -- universe of propositions and propositional
                         -- truncation
import Setoid.Sets       -- universe of sets closed under Bool and Π
import Setoid.IRSets     -- universe of sets constructed by induction
                         -- recursion
import Setoid.SeTT       -- setoid type theory rules for equality type
import Setoid.Id         -- Martin-Löf's identity type (has
                         -- definitional β rule)

import Setoid.Sets.lib   -- the inductive-inductive type (IIT) for the
                         -- universe of sets
import Setoid.Sets2.lib  -- the same IIT, but defined only using
                         -- indexed types, derviation of the simple
                         -- elimination principle
import Setoid.Sets1.lib  -- different version of the Setoid.Sets2.lib
import Setoid.Sets1      -- partial construction of the universe using
                         -- Sets1.lib
import Setoid.Sets2b.lib -- different version of the Setoid.Sets2.lib

import Abbrevs           -- abbreviations such as vz, vs, wk, _⇒_,
                         -- closure of P under Unit,Π,Σ

import Equations         -- definitional equalities validated by the
                         -- setoid model

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
import SetoidRed.Sigma
import SetoidRed.Unit
import SetoidRed.Bool
import SetoidRed.Props  -- universe of propositions and propositional truncation
import SetoidRed.Sets   -- universe of sets closed under Bool and Π
import SetoidRed.SeTT   -- setoid type theory rules for equality type
import SetoidRed.Id     -- Martin-Löf's identity type (has definitional β rule)

import AbbrevsRed
import EquationsRed
