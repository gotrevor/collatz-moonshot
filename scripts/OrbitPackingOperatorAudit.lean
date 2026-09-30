/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.FrontA.OrbitPacking

-- Independent operator review, 2026-09-22.
-- Run after building OrbitPacking: lake env lean scripts/OrbitPackingOperatorAudit.lean
#print axioms CollatzMoonshot.FrontA.OrbitPacking.weightSum_le
#print axioms CollatzMoonshot.FrontA.OrbitPacking.block_card_le
#check CollatzMoonshot.FrontA.OrbitPacking.block_card_le

-- Exact rational decay tests for five-step shells; no floating point.
example : (27 / 32 : ℚ) < 1 := by norm_num
example : (243 / 256 : ℚ) < 1 := by norm_num
