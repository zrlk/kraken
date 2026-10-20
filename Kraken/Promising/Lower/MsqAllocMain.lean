/-
**Part 2: `main_e` from the function
specifications** (env `counted (EE2 P)`, msqueue2's enqueuer) **and its
purity twin** (env `RP rel`). ISA: AArch64; machine: the
executable machine's per-thread environment semantics, partial correctness.

`main_e` is one block: the link save, `bl alloc`, node 1's data store and
`enq`'s arguments, `bl enq`, `bl alloc`, node 2's, `bl enq`, the tail. The
calls go through the existing fragment specifications placed in `msqA`
(`FragSpecEnv.of_placed`): the allocation pilot's `allocFrag_spec` (every environment; `R`
the phase's `Start`, which crosses the allocator unchanged) and the MS queue pilot's
`enqFrag_spec`/`enqFrag_pure`. The second `alloc` is at `n1 + 16`
(`Arena.alloc_chain`), so the protocol's `n2` is `n1 + 16` (`hn2`). The
data stores use msqueue2's `vc_e_str2`, as `MsqPilot.mainE_pre`.
-/
import Kraken.Promising.Lower.MsqAllocProg
import Kraken.Promising.Lower.ArenaPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.MsqAlloc

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)
open Kraken.Promising.Lower.Alloc (AllocPre AllocPost AllocSaved allocFrag_spec rpFenceMono)
open Kraken.Promising.Lower.MsqPilot (EnqPre EnqPost enqFrag_spec enqFrag_pure blTo enqFrag)
open Kraken.Promising.Lower.Arena (alloc_chain)

set_option mvcgen.warning false
set_option experimental.vcgen true

section MainA

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqA)]

local instance msqA.env : CodeEnv := ⟨layout msqA⟩

/-- The data-store block of phase `ph`. -/
def AInit (P : Params2) (ph : Ph) (p : Program) : Prop := (p = aInit1 ∧ ph = ph1 P) ∨ (p = aInit2 ∧ ph = ph2 P)

/-- Behind a data-store block: `enq`'s arguments (`x0 = q`, `x1 = n`), the
callee-saved `x19`, `x21`, `x27`, `x28` unchanged, no `dmem` word, `EL'`. -/
def AInitPost (P : Params2) (ph : Ph) (s₀ s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  s.regs.X0.toBitVec = s₀.regs.X21.toBitVec ∧ s.regs.X1.toBitVec = ph.n ∧ s.regs.X19 = s₀.regs.X19 ∧
    s.regs.X21 = s₀.regs.X21 ∧ s.regs.X27 = s₀.regs.X27 ∧ s.regs.X28 = s₀.regs.X28 ∧ NoDmem s ∧ EL' P ph σ.1

omit layout [Executable.ValidLayout (layout msqA)] in
theorem msqA_wf : Program.WF msqA := by decide +kernel

/-- Where `msqA`'s blocks sit. -/
theorem msqA_placed : Program.Placed msqA "main_e" :=
  Program.placed_of_layout msqA_wf rfl (by decide)

omit layout [Executable.ValidLayout (layout msqA)] in
/-- `main_e`'s block. -/
theorem msqA_main_block : Program.blockAt msqA "main_e" = some ⟨"main_e", mainABody, some "enq"⟩ := by
  decide +kernel

/-- The end of the enqueuer's text: the runtime's return address. -/
abbrev endEA : Int64 := (layout msqA).addrOf msqA.length

/-! ## The functions, from their fragment specifications -/

/-- **`alloc` in `msqA`**, `R` the phase's `Start` (no memory access). -/
theorem allocA (P : Params2) (ph : Ph) (hph : PhOk P ph) (n : BitVec 64) :
    FunSpecPartialEnv (SharedEnv.counted (EE2 P)) ((_root_.Executable.labels cenv).label "alloc")
      (AllocPre _ (fun σ => Start P ph σ.1) n) (AllocPost _ (fun σ => Start P ph σ.1) n) :=
  (allocFrag_spec _ _ (fun _ _ h hle => h.fence hph ((fenceMono_le_counted _ _ _).mp hle).1) n).of_placed
    msqA_placed (by decide)

/-- **`enq` in `msqA`** (the MS queue pilot's `enqFrag_spec`). -/
theorem enqA (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (ph : Ph) (hph : PhOk P ph) :
    FunSpecPartialEnv (SharedEnv.counted (EE2 P)) ((_root_.Executable.labels cenv).label "enq") (EnqPre P ph)
      (EnqPost P ph) :=
  (enqFrag_spec P hL ht ph hph).of_placed msqA_placed (by decide)

/-! ## `main_e`'s straight-line pieces -/

/-- At `main_e`: the return address in `x30`, `q = &head` in `x21`, the bump
pointer `x27 = n1` with room for **two** nodes below `x28`, no `dmem` word,
`Start` of phase 1. -/
def MainAPre (P : Params2) (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = endEA ∧ s.regs.X21.toBitVec = P.h ∧ s.regs.X27.toBitVec = P.n1 ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ P.n1 + 16 + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s ∧
    Start P (ph1 P) σ.1

omit [Executable.ValidLayout (layout msqA)] in
/-- **The link save.** -/
theorem mainA_save (P : Params2) (hL : QLocs2 P) :
    ∀ s₀ g₀, ⦃ fun s σ => MainAPre P s σ ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨aSave⟩ : EnvProgram (SharedEnv.counted (EE2 P)))
    ⦃ (fun _ s σ => Int64.ofBitVec s.regs.X19.toBitVec = endEA ∧ s.regs.X21.toBitVec = P.h ∧
        s.regs.X27.toBitVec = P.n1 ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧
        P.n1 + 16 + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s ∧ Start P (ph1 P) σ.1); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold aSave
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, hroom, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  all_goals simp [NoDmem] at *
  rename_i s σ0 σ1 hf _
  exact ⟨h30, h21, h27, hlim, hroom, ⟨hd8, hd4⟩, hT.fence (ph1_ok hL) hf.1⟩

omit [Executable.ValidLayout (layout msqA)] in
/-- **The tail**: restore the link, return with `ComE2`. -/
theorem mainA_tail (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s σ => (Int64.ofBitVec s.regs.X19.toBitVec = endEA ∧ Linked P (ph2 P) σ.1) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨aTail⟩ : EnvProgram (SharedEnv.counted (EE2 P)))
    ⦃ (fun _ _ _ => False); fun a _ σ => a = endEA ∧ ComE2 P σ.1 ⦄ := by
  intro s₀ g₀
  unfold aTail
  vcgen
  all_goals obtain ⟨⟨h19, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 σ2 hf1 hf2 _
  exact ⟨by simpa using h19, ((hT.fence (ph2_ok P) hf1.1).fence (ph2_ok P) hf2.1).1⟩

set_option hygiene false in
/-- The VCs of a data-store block (`h0`: `x0 = ph.n`; `hT`: `Start`). -/
local macro "init_vcs" v:term : tactic => `(tactic| (
  vcgen
  all_goals obtain ⟨⟨h0, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp; done)
  case vc2 =>
    rename_i s σ0 σ1 rng hnone hf1 _
    simp [h0]
    exact (vc_e_str2 hph _ (hT.fence hph hf1.1) _ (by simp [ph1, ph2, D, D2])).1
  case vc3 =>
    rename_i s σ0 σ1 rng dm σ2 σ3 σ4 hf1 hst hf2 hf3 _
    simp [h0, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hS := vc_e_str2 hph _ (hT.fence hph hf1.1) $v (by simp [ph1, ph2, D, D2])
    have hE' := hso.elim (fun h => hS.2 _ σ2.1 (by simpa [ph1, ph2, Params.dat, Params2.dat2] using h))
      (fun h => hS.2 _ σ2.1 (by simpa [ph1, ph2, Params.dat, Params2.dat2] using h))
    simp [AInitPost, NoDmem, hd8, hd4]
    exact ⟨h0, (hE'.fence hph hf2.1).fence hph hf3.1⟩
  all_goals done))

omit [Executable.ValidLayout (layout msqA)] in
/-- **A data-store block**: node `ph.n`'s data word by `vc_e_str2`, then
`enq`'s arguments. -/
theorem mainA_init (P : Params2) (ph : Ph) (hph : PhOk P ph) (p : Program) (hp : AInit P ph p) :
    ∀ s₀ g₀, ⦃ fun s σ => (s.regs.X0.toBitVec = ph.n ∧ NoDmem s ∧ Start P ph σ.1) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨p⟩ : EnvProgram (SharedEnv.counted (EE2 P))) ⦃ (fun _ s σ => AInitPost P ph s₀ s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold aInit1; init_vcs 1#128
  · unfold aInit2; init_vcs 2#128

/-! ## `main_e` -/

attribute [local simp] MachineData.lr MachineData.setLr Reg64s.setXReg in
/-- **`main_e`'s block**: four calls through their specifications, the
second `alloc` at `n1 + 16 = n2` (`alloc_chain`). -/
theorem mainA_body (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (hn2 : P.n2 = P.n1 + 16)
    (s : MachineData) (σ : (SharedEnv.counted (EE2 P)).State) (hpre : MainAPre P s σ) :
    PartialWpEnv (SharedEnv.counted (EE2 P)) mainABody (fun _ _ => False)
      (fun a _ σ => a = endEA ∧ ComE2 P σ.1) s σ := by
  have h1 := (mainA_save P hL s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
  rintro s1 σ1 ⟨h19, h21, h27, hlim, hroom, ⟨hd8, hd4⟩, hS⟩
  refine PartialWpEnv.call (allocA P _ (ph1_ok hL) P.n1) fun ra =>
    ⟨⟨by simp, by simpa using h27, by simpa using hlim, hS⟩, ?_⟩
  rintro s2 σ2 hA
  have hA2 := alloc_chain hA (by simpa using hroom)
  obtain ⟨a0, -, ⟨f19, -, f21, -, -, -, -, -, f28, fdm⟩, hS2⟩ := hA
  have h2 := (mainA_init P _ (ph1_ok hL) aInit1 (.inl ⟨rfl, rfl⟩) s2 σ2).le_wp s2 σ2
    ⟨⟨a0, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩, hS2⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
  rintro s3 σ3 ⟨i0, i1, i19, i21, i27, i28, ⟨id8, id4⟩, hE⟩
  refine PartialWpEnv.call (enqA P hL ht _ (ph1_ok hL)) fun ra =>
    ⟨⟨by simp, by simpa [i21, f21, h21] using i0, by simpa using i1, ⟨by simpa using id8, by simpa using id4⟩, hE⟩, ?_⟩
  rintro s4 σ4 ⟨⟨g19, -, g21, -, -, -, -, -, g27, g28, gdm⟩, hLk⟩
  have hA2' := hA2 0
  refine PartialWpEnv.call (allocA P _ (ph2_ok P) P.n2) fun ra => ⟨⟨by simp, ?_, ?_, hLk⟩, ?_⟩
  · rw [hn2]; simpa [g27, i27] using hA2'.2.1
  · simpa [g27, g28, i27, i28] using hA2'.2.2.1
  rintro s5 σ5 ⟨b0, -, ⟨k19, -, k21, -, -, -, -, -, -, kdm⟩, hS5⟩
  have h3 := (mainA_init P _ (ph2_ok P) aInit2 (.inr ⟨rfl, rfl⟩) s5 σ5).le_wp s5 σ5
    ⟨⟨b0, ⟨by simpa [kdm, gdm] using id8, by simpa [kdm, gdm] using id4⟩, hS5⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h3)
  rintro s6 σ6 ⟨j0, j1, j19, j21, -, -, ⟨jd8, jd4⟩, hE2⟩
  refine PartialWpEnv.call (enqA P hL ht _ (ph2_ok P)) fun ra =>
    ⟨⟨by simp, by simpa [j21, k21, g21, i21, f21, h21] using j0, by simpa using j1,
      ⟨by simpa using jd8, by simpa using jd4⟩, hE2⟩, ?_⟩
  rintro s7 σ7 ⟨⟨l19, -, -, -, -, -, -, -, -, -, -⟩, hLk2⟩
  have h4 := (mainA_tail P s7 σ7).le_wp s7 σ7
    ⟨⟨by simpa [l19, j19, k19, g19, i19, f19] using h19, hLk2⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h4
  exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h4)

/-- **`main_e` as a partial triple of the whole text**, `MainAPre` to
`ComE2` (the form `qa64CAdj_of_partialTripleEnv` takes). -/
theorem mainA_partialTripleEnv (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (hn2 : P.n2 = P.n1 + 16) :
    PartialTripleEnv (SharedEnv.counted (EE2 P)) (MainAPre P) msqA (fun _ σ => ComE2 P σ.1)
      (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := msqA) msqA [] 0 (by simp)
  rw [← msqA_placed.entry pc hpc]
  refine ((mainA_body P hL ht hn2 s σ hpre _ (msqA_placed.block _ _ msqA_main_block)).mono
    fun x hx => hx.resolve_left fun h => h.2).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
  rw [hx, msqA_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

end MainA

/-! ## The purity twin (`RP rel`) -/

section PureA

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msqA)]

local instance msqA.envP : CodeEnv := ⟨layout msqA⟩

/-- **`alloc` in `msqA` is pure** (`R = True`). -/
theorem allocA_pure (rel : Loc → Pred) (n : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "alloc")
      (AllocPre (RP rel) (fun _ => True) n) (AllocPost (RP rel) (fun _ => True) n) :=
  (@allocFrag_spec (RP rel) (rpFenceMono rel) (fun _ => True) (fun _ _ _ _ => trivial) n).of_placed
    msqA_placed (by decide)

/-- **`enq` in `msqA` is pure** (the MS queue pilot's `enqFrag_pure`). -/
theorem enqA_pure (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "enq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (enqFrag_pure rel).of_placed msqA_placed (by decide)

/-- `main_e`'s purity pre: the return address, the bump pointer `x27 = n1`
with room for two nodes, no `dmem` word. -/
def MainAPreR (n1 : BitVec 64) (s : MachineData) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = endEA ∧ s.regs.X27.toBitVec = n1 ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ n1 + 16 + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s

omit [Executable.ValidLayout (layout msqA)] in
theorem mainA_save_pure (rel : Loc → Pred) (n1 : BitVec 64) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => MainAPreR n1 s ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨aSave⟩ : EnvProgram (RP rel))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = endEA ∧ s.regs.X27.toBitVec = n1 ∧
        s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ n1 + 16 + 16 ≤ s.regs.X28.toBitVec ∧ NoDmem s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold aSave
  vcgen
  all_goals obtain ⟨⟨h30, h27, hlim, hroom, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp [NoDmem, h30, h27, hd8, hd4]
  exact ⟨by rw [← h27]; exact hlim, hroom⟩

/-- Behind a data-store block (purity): `enq`'s arguments' frame. -/
def AInitPostR (n : BitVec 64) (s₀ s : MachineData) : Prop :=
  s.regs.X1.toBitVec = n ∧ s.regs.X19 = s₀.regs.X19 ∧ s.regs.X27 = s₀.regs.X27 ∧ s.regs.X28 = s₀.regs.X28 ∧
    NoDmem s

set_option hygiene false in
/-- The purity VCs of a data-store block. -/
local macro "init_pure_vcs" : tactic => `(tactic| (
  vcgen
  all_goals obtain ⟨⟨h0, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [NoDmem, AInitPostR] at *
  case vc2 => rw [h0]; exact hd _
  case vc3 =>
    rename_i hst _
    simp [hd4] at hst
    obtain ⟨rfl, -⟩ := hst
    exact ⟨h0, hd8, hd4⟩))

omit [Executable.ValidLayout (layout msqA)] in
/-- **A data-store block is pure** for `rel` pure at the node's data word. -/
theorem mainA_init_pure (rel : Loc → Pred) (n : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v)
    (p : Program) (hp : p = aInit1 ∨ p = aInit2) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (s.regs.X0.toBitVec = n ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨p⟩ : EnvProgram (RP rel)) ⦃ (fun _ s _ => AInitPostR n s₀ s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  rcases hp with rfl | rfl
  · unfold aInit1; init_pure_vcs
  · unfold aInit2; init_pure_vcs

omit [Executable.ValidLayout (layout msqA)] in
theorem mainA_tail_pure (rel : Loc → Pred) :
    ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => Int64.ofBitVec s.regs.X19.toBitVec = endEA ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨aTail⟩ : EnvProgram (RP rel)) ⦃ (fun _ _ _ => False); fun a _ _ => a = endEA ⦄ := by
  intro s₀ g₀
  unfold aTail
  vcgen
  all_goals obtain ⟨h19, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  simpa using h19

attribute [local simp] MachineData.lr MachineData.setLr Reg64s.setXReg in
/-- **`main_e`'s block is pure**: four calls through their purity
specifications, the second `alloc` at `n1 + 16` (`alloc_chain`). -/
theorem mainA_body_pure (rel : Loc → Pred) (n1 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n1 + 16, 4⟩) v) (s : MachineData) (σ : (RP rel).State)
    (hpre : MainAPreR n1 s) :
    PartialWpEnv (RP rel) mainABody (fun _ _ => False) (fun a _ _ => a = endEA) s σ := by
  have h1 := (mainA_save_pure rel n1 s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
  rintro s1 σ1 ⟨h19, h27, hlim, hroom, ⟨hd8, hd4⟩⟩
  refine PartialWpEnv.call (allocA_pure rel n1) fun ra => ⟨⟨by simp, by simpa using h27, by simpa using hlim, trivial⟩, ?_⟩
  rintro s2 σ2 hA
  have hA2 := alloc_chain hA (by simpa using hroom)
  obtain ⟨a0, -, ⟨f19, -, -, -, -, -, -, -, f28, fdm⟩, -⟩ := hA
  have h2 := (mainA_init_pure rel n1 hd aInit1 (.inl rfl) s2 σ2).le_wp s2 σ2
    ⟨⟨a0, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
  rintro s3 σ3 ⟨-, i19, i27, i28, ⟨id8, id4⟩⟩
  refine PartialWpEnv.call (enqA_pure rel) fun ra => ⟨⟨by simp, ⟨by simpa using id8, by simpa using id4⟩⟩, ?_⟩
  rintro s4 σ4 ⟨g19, -, -, -, -, -, -, -, g27, g28, gdm⟩
  have hA2' := hA2 0
  refine PartialWpEnv.call (allocA_pure rel (n1 + 16)) fun ra => ⟨⟨by simp, ?_, ?_, trivial⟩, ?_⟩
  · simpa [g27, i27] using hA2'.2.1
  · simpa [g27, g28, i27, i28] using hA2'.2.2.1
  rintro s5 σ5 ⟨b0, -, ⟨k19, -, -, -, -, -, -, -, -, kdm⟩, -⟩
  have h3 := (mainA_init_pure rel (n1 + 16) hd2 aInit2 (.inr rfl) s5 σ5).le_wp s5 σ5
    ⟨⟨b0, ⟨by simpa [kdm, gdm] using id8, by simpa [kdm, gdm] using id4⟩⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h3)
  rintro s6 σ6 ⟨-, j19, -, -, ⟨jd8, jd4⟩⟩
  refine PartialWpEnv.call (enqA_pure rel) fun ra => ⟨⟨by simp, ⟨by simpa using jd8, by simpa using jd4⟩⟩, ?_⟩
  rintro s7 σ7 ⟨l19, -, -, -, -, -, -, -, -, -, -⟩
  have h4 := (mainA_tail_pure rel s7 σ7).le_wp s7 σ7 ⟨by simpa [l19, j19, k19, g19, i19, f19] using h19, rfl, rfl⟩
  rw [wpEnv_eq] at h4
  exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h4)

/-- **`main_e` is pure** (whole text), for release predicates pure at both
data words `[n1]`, `[n1 + 16]`. -/
theorem mainA_pure (rel : Loc → Pred) (n1 : BitVec 64) (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n1 + 16, 4⟩) v) :
    PartialTripleEnv (RP rel) (fun s _ => MainAPreR n1 s) msqA (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := msqA) msqA [] 0 (by simp)
  rw [← msqA_placed.entry pc hpc]
  refine (mainA_body_pure rel n1 hd hd2 s σ hpre _ (msqA_placed.block _ _ msqA_main_block)).mono
    fun x hx => .inl ⟨?_, trivial⟩
  rw [hx.resolve_left fun h => h.2, msqA_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

end PureA

end Kraken.Promising.Lower.MsqAlloc
