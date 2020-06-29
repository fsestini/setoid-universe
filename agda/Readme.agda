{-# OPTIONS --without-K --prop #-}

module Readme where

-- library (only defining _≡_ for now)

import lib

-- the private definitions for the setoid model

-- we don't import Setoid.lib, SetoidHom.lib

-- parts of the setoid model (these use Setoid.lib)

import Setoid.CwF
import Setoid.Pi
import Setoid.Sigma
import Setoid.Empty
import Setoid.Unit
import Setoid.Bool
import Setoid.Props  -- universe of propositions and propositional truncation
import Setoid.Sets   -- universe of sets closed under Bool and Π
import Setoid.SeTT   -- setoid type theory rules for equality type
import Setoid.Id     -- Martin-Löf's identity type (has definitional β rule)

import SetoidHom.CwF
import SetoidHom.Pi
import SetoidHom.Bool
import SetoidHom.Sigma
import SetoidHom.Id -- "surface language"
-- import SetoidHom.Sets

import SetoidRed.CwF
import SetoidRed.Pi
import SetoidRed.Sigma
import SetoidRed.Unit
import SetoidRed.Bool
import SetoidRed.Props  -- universe of propositions and propositional truncation
import SetoidRed.Sets   -- universe of sets closed under Bool and Π
import SetoidRed.SeTT   -- setoid type theory rules for equality type
import SetoidRed.Id     -- Martin-Löf's identity type (has definitional β rule)

-- abbreviations such as vz, vs, wk, _⇒_, closure of P under Unit,Π,Σ

import Abbrevs
import AbbrevsHom
import AbbrevsRed

-- definitional equalities validated by the setoid model

import Equations
import EquationsHom
import EquationsRed

-- TODO: make methatheory and object theory notations consistent,
-- something like this:
-- 
-- metatheory | object theory
-- -----------+--------------
-- →          ∣ Π, ⇒
-- Σ          | Sigma
-- proj₁      | fst
-- proj₂      | snd
-- ⊥          | Empty
-- ⊤          | Unit
-- 𝟚          | Bool
-- Prop       | P
-- Set        | U
--
-- Tr         | Trunc
-- tr         | trunc
-- 
-- ↑ps        | ElP
-- ↑pl        | LiftP
-- mk↑pl      | liftP
-- 
-- _~C        | _~C'
-- coe        | coe'
-- coh        | coh'
-- ...
