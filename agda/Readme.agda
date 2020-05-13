{-# OPTIONS --without-K --prop #-}

module Readme where

-- library (only defining _≡_ for now)

import lib

-- the private definitions for the setoid model

-- we don't import Setoid.lib

-- parts of the setoid model (these use Setoid.lib)

import Setoid.CwF
import Setoid.Empty
import Setoid.Unit
import Setoid.Bool
import Setoid.Pi
import Setoid.Sigma
import Setoid.Props  -- universe of propositions and propositional truncation

-- abbreviations

import Abbrevs

-- definitional equalities provided by the setoid model

import Equations
