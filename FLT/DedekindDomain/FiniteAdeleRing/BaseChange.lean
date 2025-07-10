/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.NumberTheory.RamificationInertia.Basic
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.RingTheory.Finiteness.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.Completion.BaseChange

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definitions

* `FiniteAdeleRing.baseChangeAlgEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

## Main theorems

* `BaseChange.isModuleTopology` : `FiniteAdeleRing B L` has the
  `FiniteAdeleRing A K`-module topology.

-/

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields. -/
noncomputable def FiniteAdeleRing.mapRingHom :
    FiniteAdeleRing A K →+* FiniteAdeleRing B L := RestrictedProduct.mapRingHom
  (fun (v : HeightOneSpectrum A) ↦ v.adicCompletion K)
  (fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
  (HeightOneSpectrum.comap A)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <| Extension.finite A K L B)
  (fun w ↦ adicCompletionComapSemialgHom A K L B (w.comap A) w rfl)
  (by
    apply Filter.Eventually.of_forall
    intro w
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    have := adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B (comap A w) w rfl
    exact Set.image_subset_iff.1 this)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def FiniteAdeleRing.mapSemialgHom :
    FiniteAdeleRing A K →ₛₐ[algebraMap K L] FiniteAdeleRing B L where
      __ := FiniteAdeleRing.mapRingHom A K L B
      map_smul' k a := by
        ext w
        simpa only [Algebra.smul_def'] using
          (adicCompletionComapSemialgHom A K L B (comap A w) w rfl).map_smul' k (a (comap A w))

open scoped TensorProduct.RightActions

noncomputable
instance BaseChange.algebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  RingHom.toAlgebra (FiniteAdeleRing.mapRingHom A K L B)

lemma FiniteAdeleRing.mapSemialgHom_continuous : Continuous (mapSemialgHom A K L B) :=
  -- This is a direct proof of the continuity of `mapSemialgHom`.
  FiniteAdeleRing.map_continuous A K L B
  -- **TODO** this needs an issue number.

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass
-- otherwise
-- #synth SMul (FiniteAdeleRing A K) (FiniteAdeleRing B L)
-- spends 2 seconds failing to find `SMul (FiniteAdeleRing A K) (adicCompletion L w)

lemma BaseChange.isModuleTopology : IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  -- This theorem lifts the local module topology at each place to the adele ring.
  -- It requires a proof that for each place `v`, the corresponding completion `L_w`
  -- has the `K_v`-module topology.
  FiniteAdeleRing.isModuleTopology_of_isModuleTopology_of_places (fun v => Place.isModuleTopology A K L B v)
  -- **TODO** this needs an issue number.

noncomputable instance : TopologicalSpace (L ⊗[K] FiniteAdeleRing A K) :=
  moduleTopology (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K)

/-- sorry #243 -/
/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
noncomputable def FiniteAdeleRing.baseChangeAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L where
  __ := AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (TensorProduct.Algebra.baseChange_bijective (FiniteAdeleRing.map_baseChange_bijective A K L B))

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def FiniteAdeleRing.baseChangeContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃cA[L] FiniteAdeleRing B L where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  continuous_toFun := by
    -- The forward map is a base change of the map `mapSemialgHom`.
    -- We prove it's continuous by applying the theorem that the base change of a
    -- continuous map is continuous, to the proof that `mapSemialgHom` is continuous.
    apply TensorProduct.Algebra.baseChange_continuous
    exact FiniteAdeleRing.map_continuous A K L B
  continuous_invFun := by
    -- The proof for the inverse function follows a symmetric argument.
    -- The inverse of the base change is also a base change of a continuous map.
    -- We apply the same general theorem to the proof of continuity for the inverse map.
    apply TensorProduct.Algebra.baseChange_continuous
    exact FiniteAdeleRing.map_continuous_symm A K L B
  -- **TODO** needs issue number

noncomputable instance baseChangeAlgebra : Algebra K (FiniteAdeleRing B L) :=
  RingHom.toAlgebra <| (algebraMap L _).comp (algebraMap K L)

noncomputable instance baseChangeScalarTower :
    IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  nth_rw 2 [RingHom.algebraMap_toAlgebra]
  symm
  exact SemialgHom.commutes (FiniteAdeleRing.mapSemialgHom A K L B) x

end IsDedekindDomain
