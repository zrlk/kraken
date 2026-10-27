/-
**The abort path is off the transfer sites** (AArch64), at any layout: the
`hns` premises of `abIn_steps` (`Spike/Lib/Rt/A64AbDt.lean`) and
`stubDt_closed` (`Spike/Lib/Rt/A64StubDt.lean`) on the paths to the write
and heap stubs, from their phase checks (`abortPhWriteOk`,
`abortPhHeapOk`, parts of A7's `tailOffC`) and, for the stub's exit call
(an abort site, so not checked off the sites), the sites' distinctness.

- `abIn_noSite_write`, `abIn_noSite_heap`: `AbIn … .write`/`.heap` (any
  region and frame condition) off the transfer sites;
- `abort_site_off`: distinct sites (`sitesOf`, `Nodup`) put every abort
  site off the transfer sites; `exit_off_ofPlaceOK`, `lab_toNat_ofPlaceOK`:
  at the record, the canonical abort labels at their `codeOf` addresses;
- `stubDt_noSite`: a stub's `StubDt` off the transfer sites, from the
  `write` call's `phOne`, the shared block's `blkPh` and its exit call off
  the transfer sites (`hex`);
- `abortPhWriteOk_ofPlaceOK`, `abortPhHeapOk_ofPlaceOK`: the stubs' phase checks at the
  record; `stubDt_noSite_write_ofPlaceOK`, `stubDt_noSite_heap_ofPlaceOK`,
  `abIn_noSite_write_ofPlaceOK`, `abIn_noSite_heap_ofPlaceOK`: at the record, from the
  stubs' phase checks and distinct sites with the canonical abort labels.
-/
import Spike.Lib.Rt.A64AbDt
import Spike.Lib.Rt.A64PrintNoSite

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib (Region)
open Spike.Lib.A64Consumer (blkPh)
open Spike.Lib.A64.PhRec (okPc ph μ)
open Spike.Lib.A64.Abort.Disp (DN DX)
open Scc.Cert.Rt.A64.Print (add0)
open Scc.Cert.Link.A64 (codeOf)

/-! ## The dispatcher and the stubs' entries -/

/-- **The abort path to the write stub is off the transfer sites**, from
its phase check at the record (any region and frame condition). -/
theorem abIn_noSite_write (L : RuntimeLayout) {RA : Region} {C : MachineData → Prop}
    (h : StubW.abortPhWriteOk (okPc L) (ph L) L.lab = true) :
    ∀ s, AbIn L.exe L.endPc RA C .write s → Kernel.siteAt abi (μ L) s = none := by
  simp only [StubW.abortPhWriteOk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨d0, t1, j1, t2, j2, t3, j3, t4, g4, b0, n1, n1b, b1, -⟩ := h
  rintro s (⟨i, hs⟩ | ⟨j, hs⟩) <;> apply siteAt_of_okPc
  · cases i
    case e => exact blkSt_okPc d0 (add0 _).symm hs
    case t1 => exact blkSt_okPc t1 (add0 _).symm hs
    case j1 => exact blkSt_okPc j1 (by simp only [dpc, Int64.add_assoc]; rfl) hs
    case t2 => exact blkSt_okPc t2 (add0 _).symm hs
    case j2 => exact blkSt_okPc j2 (by simp only [dpc, Int64.add_assoc]; rfl) hs
    case t3 => exact blkSt_okPc t3 (add0 _).symm hs
    case j3 => exact blkSt_okPc j3 (by simp only [dpc, Int64.add_assoc]; rfl) hs
    case t4 => exact blkSt_okPc t4 (add0 _).symm hs
    case g4 => exact blkSt_okPc g4 (add0 _).symm hs
    case dead => obtain ⟨-, -, -, σ0, h, -⟩ := hs; exact h.elim
    all_goals obtain ⟨-, -, -, σ0, ⟨-, hj⟩, -⟩ := hs; simp [dxCode] at hj
  · cases j
    case e => exact blkSt_okPc b0 (add0 _).symm hs
    case n1 =>
      obtain ⟨-, -, -, hpc, -⟩ := hs
      rw [hpc]
      have := (Bool.and_eq_true _ _ ▸ n1).1
      rwa [add0] at this
    case n1b =>
      obtain ⟨-, -, -, hpc, -⟩ := hs
      rw [hpc]
      exact (Bool.and_eq_true _ _ ▸ n1b).1
    case n2 => exact blkSt_okPc b1 (by simp only [Int64.add_assoc]; rfl) hs

/-- **The abort path to the heap stub is off the transfer sites**, from its
phase check at the record (any region and frame condition). -/
theorem abIn_noSite_heap (L : RuntimeLayout) {RA : Region} {C : MachineData → Prop}
    (h : StubW.abortPhHeapOk (okPc L) (ph L) L.lab = true) :
    ∀ s, AbIn L.exe L.endPc RA C .heap s → Kernel.siteAt abi (μ L) s = none := by
  simp only [StubW.abortPhHeapOk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨d0, t1, j1, t2, g2, b0, n1, n1b, b1, -⟩ := h
  rintro s (⟨i, hs⟩ | ⟨j, hs⟩) <;> apply siteAt_of_okPc
  · cases i
    case e => exact blkSt_okPc d0 (add0 _).symm hs
    case t1 => exact blkSt_okPc t1 (add0 _).symm hs
    case j1 => exact blkSt_okPc j1 (by simp only [dpc, Int64.add_assoc]; rfl) hs
    case t2 => exact blkSt_okPc t2 (add0 _).symm hs
    case g2 => exact blkSt_okPc g2 (add0 _).symm hs
    case dead => obtain ⟨-, -, -, σ0, h, -⟩ := hs; exact h.elim
    all_goals obtain ⟨-, -, -, σ0, ⟨-, hj⟩, -⟩ := hs; simp [dxCode] at hj
  · cases j
    case e => exact blkSt_okPc b0 (add0 _).symm hs
    case n1 =>
      obtain ⟨-, -, -, hpc, -⟩ := hs
      rw [hpc]
      have := (Bool.and_eq_true _ _ ▸ n1).1
      rwa [add0] at this
    case n1b =>
      obtain ⟨-, -, -, hpc, -⟩ := hs
      rw [hpc]
      exact (Bool.and_eq_true _ _ ▸ n1b).1
    case n2 => exact blkSt_okPc b1 (by simp only [Int64.add_assoc]; rfl) hs

/-! ## The abort sites -/

/-- **Distinct sites put an abort site off the transfer sites**: its label
resolves, and neither transfer site is at its address. -/
theorem abort_site_off {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {ss : List Nat}
    (hs : Scc.Cert.Rt.A64.sitesOf lo prog Λ = some ss) (hnd : ss.Nodup) (k : Scc.Sem.AbortKind) :
    ∃ a, codeOf lo prog (Λ.abortLbl k) = some a ∧ codeOf lo prog "scc_rt_take_site" ≠ some a ∧
      codeOf lo prog "scc_rt_release_site" ≠ some a := by
  simp only [Scc.Cert.Rt.A64.sitesOf, Scc.Cert.Rt.A64.sitesBy, Scc.Cert.Rt.A64.siteLabels, List.map,
    List.cons_append, List.nil_append] at hs
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hs
  obtain ⟨a1, h1, _, ⟨a2, h2, _, ⟨a3, h3, _, ⟨a4, h4, _, ⟨a5, h5, _, ⟨a6, h6, _, ⟨a7, h7, _, rfl, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hs
  rw [h1, h2]
  cases k
  · exact ⟨a3, h3, by simp_all, by simp_all⟩
  · exact ⟨a4, h4, by simp_all, by simp_all⟩
  · exact ⟨a5, h5, by simp_all, by simp_all⟩
  · exact ⟨a7, h7, by simp_all, by simp_all⟩
  · exact ⟨a6, h6, by simp_all, by simp_all⟩

/-! ## A stub's tail -/

/-- **A stub's write tail is off the transfer sites**, from the `write`
call's pc off the sites (`hsvc`), the shared block's phase check (`hb2`) and
the exit call off the transfer sites (`hex`). -/
theorem stubDt_noSite (L : RuntimeLayout) {st : Abort.Stub}
    (hsvc : okPc L (L.lab st.entry + Int64.ofNat (4 * 7)).toBitVec.toNat = true)
    (hb2 : blkPh (okPc L) (ph L) (fun _ => false) L.lab (L.lab st.entry + Int64.ofNat (4 * 8)) 0 Abort.b2 = true)
    (hex : (μ L).site .take ≠ some (L.lab st.exit).toBitVec.toNat ∧
      (μ L).site .release ≠ some (L.lab st.exit).toBitVec.toNat) :
    ∀ s, StubDt L.exe L.endPc L.lab st s → Kernel.siteAt abi (μ L) s = none := by
  have e0 : Abort.pcSvc L.lab st = L.lab st.entry + Int64.ofNat (4 * 7) := by
    simp only [Abort.pcSvc, Int64.add_assoc]; rfl
  have e : ∀ k, k < 3 → Abort.pcSvc L.lab st + Int64.ofNat (4 * (k + 1)) =
      L.lab st.entry + Int64.ofNat (4 * 8) + Int64.ofNat (4 * k) := by
    intro k hk
    rw [e0, Int64.add_assoc, Int64.add_assoc]
    congr 1
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
  have hl : Abort.b2.length = 3 := by decide
  rintro s ⟨-, -, ⟨hpc, -⟩ | ⟨hpc, -⟩ | hpc | hpc | ⟨hpc, -⟩⟩
  · apply siteAt_of_okPc; rw [hpc, e0]; exact hsvc
  · apply siteAt_of_okPc
    rw [hpc, show Abort.pcSvc L.lab st + 4 = Abort.pcSvc L.lab st + Int64.ofNat (4 * (0 + 1)) from rfl,
      e 0 (by omega)]
    exact okPc_of_blkPh hb2 (by omega)
  · apply siteAt_of_okPc
    rw [hpc, show Abort.pcSvc L.lab st + 4 + 4 = Abort.pcSvc L.lab st + Int64.ofNat (4 * (1 + 1)) by
      rw [Int64.add_assoc]; rfl, e 1 (by omega)]
    exact okPc_of_blkPh hb2 (by omega)
  · apply siteAt_of_okPc
    rw [hpc, show Abort.pcSvc L.lab st + 4 + 4 + 4 = Abort.pcSvc L.lab st + Int64.ofNat (4 * (2 + 1)) by
      rw [Int64.add_assoc, Int64.add_assoc]; rfl, e 2 (by omega)]
    exact okPc_of_blkPh hb2 (by omega)
  · refine Kernel.siteAt_eq_none_iff.mpr ⟨fun he => hex.1 ?_, fun he => hex.2 ?_⟩ <;> rw [← hpc] <;> exact he

/-! ## From the placement check -/

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true) (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **A resolved label's address** at the record of an output passing
`placeOK` is its `codeOf` address. -/
theorem lab_toNat_ofPlaceOK {l : String} {a : Nat} (ha : codeOf Λ.code.lo o.prog l = some a) :
    ((RuntimeLayout.ofPlaceOK h i).lab l).toBitVec.toNat = a := by
  have hlab := Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
    (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha
  have hlt : a < 2 ^ 64 := Nat.lt_of_le_of_lt (PhRec.le_codeEnd_of_codeOf ha) (PhRec.codeEnd_lt h i)
  have hlab' : (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a := hlab
  rw [hlab']
  simp [Nat.mod_eq_of_lt hlt]

/-- **The write abort path's phase check** at the record's `okPc`/`ph` and
labels of an output passing `placeOK`, from A7's `tailOffC`. -/
theorem abortPhWriteOk_ofPlaceOK :
    StubW.abortPhWriteOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true :=
  StubW.abortPhWriteOk_of_tailPhOk (tailPhOk_ofPlaceOK h i)

/-- **The heap abort path's phase check** at the record's `okPc`/`ph` and
labels of an output passing `placeOK`, from A7's `tailOffC`. -/
theorem abortPhHeapOk_ofPlaceOK :
    StubW.abortPhHeapOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true :=
  StubW.abortPhHeapOk_of_tailPhOk (tailPhOk_ofPlaceOK h i)

/-- **An abort exit call is off the transfer sites** at the record of an
output passing `placeOK` (the sites distinct, the abort labels canonical). -/
theorem exit_off_ofPlaceOK (k : Scc.Sem.AbortKind) :
    (μ (RuntimeLayout.ofPlaceOK h i)).site .take ≠
        some ((RuntimeLayout.ofPlaceOK h i).lab (Scc.Cert.Link.abortName k)).toBitVec.toNat ∧
      (μ (RuntimeLayout.ofPlaceOK h i)).site .release ≠
        some ((RuntimeLayout.ofPlaceOK h i).lab (Scc.Cert.Link.abortName k)).toBitVec.toNat := by
  obtain ⟨ss, hs, hnd⟩ := sites_nodup_of_placeOKAt h
  obtain ⟨a, ha, ht, hr⟩ := abort_site_off hs hnd k
  rw [abortLbl_of_placeOKAt h] at ha
  rw [lab_toNat_ofPlaceOK h i ha]
  exact ⟨ht, hr⟩

/-- **The write stub's tail is off the transfer sites** at the record of an
output passing `placeOK`, from A7's `tailOffC`. -/
theorem stubDt_noSite_write_ofPlaceOK :
    ∀ s, StubDt (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc
      (RuntimeLayout.ofPlaceOK h i).lab Abort.write s →
        Kernel.siteAt abi (μ (RuntimeLayout.ofPlaceOK h i)) s = none := by
  have hw := StubW.abortPhWriteOk_of_tailPhOk (tailPhOk_ofPlaceOK h i)
  simp only [StubW.abortPhWriteOk, Bool.and_eq_true, and_assoc] at hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, psvc, pb2, -⟩ := hw
  exact stubDt_noSite _ (Bool.and_eq_true _ _ ▸ psvc).1 pb2 (exit_off_ofPlaceOK h i .writeErr)

/-- **The heap stub's tail is off the transfer sites** at the record of an
output passing `placeOK`, from A7's `tailOffC`. -/
theorem stubDt_noSite_heap_ofPlaceOK :
    ∀ s, StubDt (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc
      (RuntimeLayout.ofPlaceOK h i).lab Abort.heap s →
        Kernel.siteAt abi (μ (RuntimeLayout.ofPlaceOK h i)) s = none := by
  have hw := StubW.abortPhHeapOk_of_tailPhOk (tailPhOk_ofPlaceOK h i)
  simp only [StubW.abortPhHeapOk, Bool.and_eq_true, and_assoc] at hw
  obtain ⟨-, -, -, -, -, -, -, -, -, psvc, pb2, -⟩ := hw
  exact stubDt_noSite _ (Bool.and_eq_true _ _ ▸ psvc).1 pb2 (exit_off_ofPlaceOK h i .heap)

/-- **The abort path to the write stub is off the transfer sites** at the
record of an output passing `placeOK`, from A7's `tailOffC`. -/
theorem abIn_noSite_write_ofPlaceOK {RA : Region}
    {C : MachineData → Prop} :
    ∀ s, AbIn (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc RA C .write s →
      Kernel.siteAt abi (μ (RuntimeLayout.ofPlaceOK h i)) s = none :=
  abIn_noSite_write _ (StubW.abortPhWriteOk_of_tailPhOk (tailPhOk_ofPlaceOK h i))

/-- **The abort path to the heap stub is off the transfer sites** at the
record of an output passing `placeOK`, from A7's `tailOffC`. -/
theorem abIn_noSite_heap_ofPlaceOK {RA : Region}
    {C : MachineData → Prop} :
    ∀ s, AbIn (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc RA C .heap s →
      Kernel.siteAt abi (μ (RuntimeLayout.ofPlaceOK h i)) s = none :=
  abIn_noSite_heap _ (StubW.abortPhHeapOk_of_tailPhOk (tailPhOk_ofPlaceOK h i))

end Place

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.stubDt_noSite_write_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stubDt_noSite_write_ofPlaceOK

/--
info: 'Spike.Lib.A64.Rt.abIn_noSite_write_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms abIn_noSite_write_ofPlaceOK

end Spike.Lib.A64.Rt
