/-
**hello.w's refusal blocks inside the third level** (AArch64; part 6; the hello twin
of `Spike/Lib/A64WakeRefBlk.lean`): `cb` (`.sp6 + 4 · 26`), `.clone13`'s `cl` and `.1_spawnfail5`'s `flB`, the nine
pcs from `.sp6 + 104`, inside `RootWX.W2H ∧ X2H` (the root's `W2I ∧ X2I`) under no `TakeCKS` move. `W2H`'s `Wf` by
`WakeWf.blkW_wf`: `SFactsSt2` at `ownGH` by `WcSp4W.blk_cH` at `own2bH … 0`, where `ownGH` agrees with it
(`agreeBlkH`); the write abort by `blkW_dispAbI` at `instOk2bPH`; the blocks inside the threads abort phase
`AcH` (`hac`); the source's frames placed (`hpl`). `X2H` off the clone's pc and the take site (`x2H_off`).

- `atLH`, `of_atLH`: a property of a label's address in helloProg, decided on `codeT`.
- `blkFactsH`: the blocks' pcs, `ph2bH` `0` and off the sites there; `scc_rt_abort` at `ph2bH` `0`.
- `dChkAH`, `dChkAH_sound`: the write abort's dispatcher check on helloProg's labels (wake's `dChkAW`).
- `sp13_ne_sp15`: `scc_rt_alloc_tcb`'s and the refusal's return addresses differ.
- `blk1H`: one block, generic in its node (`hJ`, `hac`, `hpl` read its entry facts).

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefPre
import Spike.Lib.A64HelloRefPh
import Spike.Lib.A64HelloWcSp4W
import Spike.Lib.A64HelloOwnGEq
import Spike.Lib.A64HelloSpawnFailAC
import Spike.Lib.A64HelloH1A
import Spike.Lib.A64HelloRootWX
import Spike.Lib.A64HelloH2Inv
import Spike.Lib.A64WakeRefBlk
import Spike.Lib.A64HelloSpawnPl
import Spike.Lib.A64HelloSpawnFailS

namespace Spike.Lib.A64.HelloPh.RefBlkH

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (codeT_eq)
open Spike.Lib (Region FragS Arena)
open Spike.Lib.A64.Flow (ND BlkW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.A64.WakePh (inPc x30At)
open Spike.Lib.LowerA64 (labC blkLabs)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.WakeRefStub (toNat_off toNat_ofNat)

/-- A property `p` of label `l`'s address in helloProg, decided on `codeT`. -/
def atLH (l : String) (p : Nat → Bool) : Bool :=
  match Scc.Cert.Rt.A64.codeT lo SccCode.helloProg l with
  | some x => p x
  | none => false

theorem of_atLH {l : String} {p : Nat → Bool} (h : atLH l p = true) :
    ∃ x, codeOf lo SccCode.helloProg l = some x ∧ p x = true := by
  unfold atLH at h; rw [codeT_eq] at h
  split at h
  · next x hx => exact ⟨x, hx, h⟩
  · cases h

/-- **The refusal blocks' pcs**: `.clone13` at `.sp6 + 108`, `.1_spawnfail5` at `.sp6 + 132`, the nine pcs from
`.sp6 + 104` below `.stack_grow` with `ph2bH` `0` and off the sites, the take site below `.sp6`; `scc_rt_abort`
at `ph2bH` `0`, below `scc_rt_thr_worker`. -/
def blkFactsH : Bool :=
  atLH ".L22_wc_main.sp6" (fun x => decide (x + 148 < 2 ^ 63) &&
    atLH (pfxM ++ ".clone13") (fun y => y == x + 108) && atLH (pfxM ++ ".1_spawnfail5") (fun y => y == x + 132) &&
    atLH ".L22_wc_main.stack_grow" (fun y => decide (x + 136 < y ∧ y < 2 ^ 63)) &&
    atLH siteL (fun y => decide (y < x)) &&
    (List.range 9).all fun j => ph2bHC (x + 104 + 4 * j) == 0 && okC (x + 104 + 4 * j)) &&
  atLH "scc_rt_abort" (fun x => ph2bHC x == 0 && decide (x < 2 ^ 63) &&
    atLH "scc_rt_thr_worker" (fun y => decide (x < y ∧ y < 2 ^ 63)))

theorem blkFactsH_ok : blkFactsH = true := by decide +kernel

/-- **The write abort's dispatcher check on helloProg's labels** (wake's `dChkAW`): the labels resolve and
`dChkA` holds at the code labels. -/
def dChkAH (l : Label) (k : Nat) (E T D : List Nat) (blk : List Directive) : Bool :=
  (l :: blkLabs blk ++ abLabs).all (fun x => (codeOf lo SccCode.helloProg x).isSome) &&
    Spike.Lib.A64.WakeWf.dChkA (labC lo SccCode.helloProg)
      (labC lo SccCode.helloProg l + Int64.ofNat (4 * k)) E T D blk

section Lab

variable {lab : Label → Int64} (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- `dChkAH` gives `dChkA` at any labels agreeing with the code labels. -/
theorem dChkAH_sound {l : Label} {k : Nat} {E T D : List Nat} {blk : List Directive}
    (h : dChkAH l k E T D blk = true) :
    Spike.Lib.A64.WakeWf.dChkA lab (lab l + Int64.ofNat (4 * k)) E T D blk = true := by
  simp only [dChkAH, Bool.and_eq_true] at h
  have hl := Spike.Lib.A64.HelloWf.lab_labCH hlab h.1
  rw [Spike.Lib.A64.WakeWf.dChkA_congr (fun x hx => hl x (by simp [hx])) (fun x hx => hl x (by simp [hx])),
    hl l (by simp)]
  exact h.2

theorem toNat_labH {l : Label} {x : Nat} (h : codeOf lo SccCode.helloProg l = some x) (hx : x < 2 ^ 64) :
    (lab l).toBitVec.toNat = x := by
  rw [hlab l x h]; show (BitVec.ofNat 64 x).toNat = x; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- **`scc_rt_alloc_tcb`'s abort return address is not the refusal's.** -/
theorem sp13_ne_sp15 : (lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec ≠ (lab ".L22_wc_main.sp15").toBitVec := by
  rw [hlab _ 2164996 (by rw [← codeT_eq]; decide +kernel), hlab _ 2169912 (by rw [← codeT_eq]; decide +kernel)]
  decide

end Lab

/-! ## The source placed along the blocks -/

open Spike.Lib.A64.Flow.Worker.Hello.SpawnFail (MSS) in
/-- **main's source placed at every block state** (wake's `WakeSrcCtl.placedSE_blkMS`): the five packet words at
the slots `MSS` names at the node's entry, kept by the block (`hk`), represented under `lbl` (`hsl`, `hcA`,
`hme`). -/
theorem placedSE_blkMSS {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word}
    {cP : Spike.Lib.Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {blk : List Directive} (hsrc : Spike.Lib.HelloMainPreSrc.SpawnSrcH l ws cP)
    (hsl : Spike.Lib.HelloMainPreSrc.SlRep lbl ws sl.1.toNat sl.2.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat)
    (hcA : lbl l = some cA.toNat) (hme : lbl (Spike.Lib.WakeT1.mainTidLbl 2) = some me.toNat)
    (o0 : R.Off (-144)) (o2 : R.Off (-128)) (o3 : R.Off (-120)) (o4 : R.Off (-104)) (o5 : R.Off (-112))
    (hJ : ∀ σ c, n.J σ c → c = cP ∧ MSS sl cA me σ)
    (hk : ([-144, -128, -120, -104, -112] : List Int).all
      (fun j => Spike.Lib.WakeSrcCtl.keepsSlot j n.o blk) = true) :
    BlkW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  obtain ⟨rfl, h0, h2, h3, h4, h5⟩ := hJ σ c hj
  obtain ⟨lr, rfl, hl, -, hw2, hw3⟩ := hsl
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hk
  obtain ⟨k0, k2, k3, k4, k5⟩ := hk
  refine ⟨Spike.Lib.A64.HelloPh.SpawnPl.placedSE_spawnAtH (.slot (R.addr (-144)).toNat)
    (.slot (R.addr (-128)).toNat) (.slot (R.addr (-120)).toNat) (.slot (R.addr (-104)).toNat)
    (.slot (R.addr (-112)).toNat) hsrc ?_ ?_ ?_ ?_ ?_, fun _ h => h⟩
  · refine ⟨_, Spike.Lib.WakeSrcCtl.placeVal_slot_abs hA o0, by decide, sl.1.toNat,
      by simp [Scc.Sem.wordAddr, hl], ?_⟩
    rw [Spike.Lib.WakeSrcCtl.arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k0, h0]; rfl
  · refine ⟨_, Spike.Lib.WakeSrcCtl.placeVal_slot_abs hA o2, by decide, ?_⟩
    rw [Spike.Lib.WakeSrcCtl.arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k2, h2]; exact hw2
  · refine ⟨_, Spike.Lib.WakeSrcCtl.placeVal_slot_abs hA o3, by decide, ?_⟩
    rw [Spike.Lib.WakeSrcCtl.arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k3, h3]; exact hw3
  · exact ⟨_, Spike.Lib.WakeSrcCtl.placeVal_slot_abs hA o4,
      by rw [Spike.Lib.WakeSrcCtl.arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k4, h4]; exact hcA⟩
  · exact ⟨_, Spike.Lib.WakeSrcCtl.placeVal_slot_abs hA o5,
      by rw [Spike.Lib.WakeSrcCtl.arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k k5, h5]; exact hme⟩

/-- The three blocks keep the packet's five slots (they store only to `-32`). -/
theorem keeps_fNS : ∀ blk ∈ [Spike.Lib.A64.Flow.Worker.Hello.Child.cb pfxM,
    Spike.Lib.A64.Flow.Worker.Hello.Parent.cl pfxM, Spike.Lib.A64.Flow.Worker.Hello.SpawnFail.flB],
    ([-144, -128, -120, -104, -112] : List Int).all
      (fun j => Spike.Lib.WakeSrcCtl.keepsSlot j Spike.Lib.A64.Flow.Worker.Hello.Parent.oP blk) = true := by
  decide +kernel

section Gen

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)
  {a : BitVec 64} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {endX : Int64} {lbl' : Lbl} {lsize' : Lsize}

include hp hlo hΛ hlab hsite

/-- **One refusal block inside `W2H ∧ X2H`**, no `TakeCKS` move: its pcs among the nine from `.sp6 + 104`
(`hlb`), its states in `AcH` (`hac`), its controls not a `ret` with their runs well formed (`hJ`), its frames
placed (`hpl`), `ownGH` `own2bH … 0` where its run ends (`hlast`). -/
theorem blk1H {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {nd : ND} {blk : List Directive} {lb : Label} {k : Nat}
    (hb : Scc.Cert.Rt.A64.blockAt SccCode.helloProg lb k blk = true) (he : L.lab lb + Int64.ofNat (4 * k) = nd.pc)
    (hok : Spike.Lib.A64.Flow.okBlk (-144) 0 nd.o blk = true)
    (hcls : (blk.all fun d => (Spike.Lib.A64.Flow.classify d).isSome) = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true)
    (hphb : Spike.Lib.A64Consumer.blkPh (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg L.Λ) ph2bH
      (fun _ => false) L.lab (L.lab lb + Int64.ofNat (4 * k)) 0 blk = true)
    {Es : List Nat} (hchk : dChkAH lb k Es [] [] blk = true)
    (hE : ∀ σ c, nd.J σ c → ∀ j, j < blk.length → j ∈ Es →
      (Spike.Lib.A64.Flow.arun L.lab (blk.take (j + 1)) ⟨nd.pc, nd.o, σ⟩).σ.regs.X0 ≠ 4)
    (hac : ∀ (s : State) σ c j m, nd.J σ c → j < blk.length →
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨nd.pc, nd.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨nd.pc, nd.o, σ⟩).σ →
      Spike.Lib.A64.HelloWf.AcH L.lab pfxM { s with st := (m, nd.pc + Int64.ofNat (4 * j)) })
    (hJ : ∀ σ c, nd.J σ c →
      (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf Spike.Lib.HelloSrc.helloSrc c [])
    (hpl : BlkW (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F
      nd blk)
    (d : Nat) (hd : d + blk.length ≤ 9)
    (hlb : ∀ X, codeOf lo SccCode.helloProg ".L22_wc_main.sp6" = some X →
      ∃ x, codeOf lo SccCode.helloProg lb = some x ∧ x + 4 * k = X + 104 + 4 * d)
    (hlast : ∀ σ c, nd.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab blk ⟨nd.pc, nd.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab blk ⟨nd.pc, nd.o, σ⟩).σ →
      s.st = (m, (Spike.Lib.A64.Flow.arun L.lab blk ⟨nd.pc, nd.o, σ⟩).pc) →
        (∀ X, codeOf lo SccCode.helloProg ".L22_wc_main.sp6" = some X → ∃ q < 9, pcOf s = X + 104 + 4 * q) ∨
        (pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat ∧ x30At L ".L22_wc_main.sp15" s)) :
    BlkW (fun s c => RootWX.W2H L a ar Spike.Lib.HelloSrc.helloSrc Dt (ClH L) Ctx lbl lsize s c [] ∧
        Spike.Lib.HelloH2Inv.X2H L (L.lab siteL) endX lbl' lsize' s c [])
      (Spike.Lib.A64ConsumerA.TakeCKS (L.lab siteL) (ClH L)) L.exe L.endPc R F nd blk := by
  obtain ⟨X, hX, hF⟩ := of_atLH (Bool.and_eq_true _ _ ▸ blkFactsH_ok).1
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hF
  obtain ⟨⟨⟨⟨⟨hX1, -⟩, -⟩, hG⟩, hT⟩, hph9⟩ := hF
  obtain ⟨G, hG, hXG⟩ := of_atLH hG
  obtain ⟨T, hT, hTX⟩ := of_atLH hT
  have eX := toNat_labH hlab hX (by omega)
  have hq : ∀ j < blk.length, ∃ q < 9, (nd.pc + Int64.ofNat (4 * j)).toBitVec.toNat = X + 104 + 4 * q := by
    intro j hj
    obtain ⟨x, hx, hxk⟩ := hlb X hX
    refine ⟨d + j, by omega, ?_⟩
    rw [← he, hlab _ _ hx, ← Int64.ofNat_add, ← Int64.ofNat_add, toNat_ofNat (by omega)]; omega
  have hown : ∀ (s : State) q, q < 9 → pcOf s = X + 104 + 4 * q → ownGH L a s = own2bH L a 0 := by
    intro s q hq hs
    have hg : Good2bH L s := .inr (.inl (by
      unfold inPc; rw [eX, toNat_labH hlab hG (by simp at hXG; omega), hs]
      simp at hXG; omega))
    have := hph9 q hq
    simp only [beq_iff_eq] at this
    rw [ownGH_2b hlab hg, hs, ph2bH_eq, this.1]
  obtain ⟨A, hA, hAF⟩ := of_atLH (Bool.and_eq_true _ _ ▸ blkFactsH_ok).2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hAF
  obtain ⟨W, hW, hAW⟩ := of_atLH hAF.2
  simp only [decide_eq_true_eq] at hAW
  have hab : ∀ s : State, pcOf s = (L.lab "scc_rt_abort").toBitVec.toNat →
      x30At L ".L22_wc_main.sp15" s → ownGH L a s = own2bH L a 0 := by
    intro s hs hx
    have eA := toNat_labH hlab hA (by omega)
    have hg : Good2bH L s := .inr (.inr ⟨by
      unfold inPc; rw [hs, toNat_labH hlab hW (by omega), eA]; omega, hx,
      fun ⟨h13, _⟩ => sp13_ne_sp15 hlab (h13.symm.trans hx)⟩)
    rw [ownGH_2b hlab hg, hs, ph2bH_eq, eA, hAF.1.1]
  have hag := Spike.Lib.A64.HelloPh.WcSp4W.agreeBlkH (a := a) (F := F) hsite
    (Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) he) hok hR hal (by omega) (by omega)
    (fun j hj => by
      obtain ⟨q, -, e⟩ := hq j hj
      rw [e, toNat_labH hlab hT (by simp at hTX; omega)]; simp at hTX; omega)
    (fun σ c _ j hj s m _ hs => by
      obtain ⟨q, hq9, e⟩ := hq j hj
      exact hown s q hq9 (by unfold pcOf; rw [hs]; exact e))
    (fun σ c hJc s m hA' hs => (hlast σ c hJc s m hA' hs).elim
      (fun h => let ⟨q, hq9, e⟩ := h X hX; hown s q hq9 e) fun h => hab s h.1 h.2)
  have hokc : ∀ j < blk.length, okC (nd.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    obtain ⟨q, hq9, e⟩ := hq j hj
    have := hph9 q hq9
    simp only [beq_iff_eq] at this
    rw [e]; exact this.2
  have hst := Spike.Lib.A64.HelloPh.WcSp4W.blk_cH hp hlo hsite hΛ (own2bH L a 0) (Λ := L.Λ)
    (rS := ⟨0, 0⟩) hb he hok hR hal (by omega) (by omega) hcls hnr hokc hag
  have hI2 := instOk2bPH hp hlo a (rS := ⟨0, 0⟩) hsite
  have hW := Spike.Lib.A64.WakeWf.blkW_wf (ar := ar) (p := Spike.Lib.HelloSrc.helloSrc)
    (Cl := ClH L) (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (fs := [])
    (Spike.Lib.A64.WakePh.CalWf.blkW_dt (Dt := Dt) hst)
    (Spike.Lib.A64.WakeWf.blkW_dispAbI hI2 (hp ▸ hb) he hok hR hal (by omega) (by omega)
      ⟨by decide, by omega, by omega⟩ hphb hnr (dChkAH_sound hlab hchk)
      (fun _ _ _ _ _ _ _ h => by simp at h) hE (fun _ _ _ _ _ h => by simp at h))
    (fun s σ c _ _ _ _ _ _ hj j hk m hA _ =>
      ⟨Spike.Lib.A64ConsumerA.AcSt.of_ac (hac s σ c j m hj hk hA), fun _ h => h⟩)
    (fun _ h => ⟨h.2.1, h.2.2⟩)
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      ⟨⟨fun _ => (hJ σ c a7).1, (hpl s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1, (hJ σ c a7).2⟩, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.blkW_noWrC (Spike.Lib.A64.AllocG.blkW_noWr hI2 (hp ▸ hb) he hok hR hal
      (by omega) (by omega)))
    (Spike.Lib.A64.WakeWf.blkW_abortWf (fun j hj s _ _ h3 => (hI2.off s (by
      rw [okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokc j hj)).1))
  intro s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
  obtain ⟨q, hq9, hpcj⟩ := hq j hj
  have hc : pcOf { s with st := (m, nd.pc + Int64.ofNat (4 * j)) } ≠ Spike.Lib.HelloPreA.clonePcH L := by
    show _ ≠ (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 25)).toBitVec.toNat
    unfold pcOf; rw [hpcj, hlab _ _ hX, toNat_off _ _ (by omega)]; omega
  have ha : pcOf { s with st := (m, nd.pc + Int64.ofNat (4 * j)) } ≠ (L.lab siteL).toBitVec.toNat := by
    unfold pcOf; rw [hpcj, toNat_labH hlab hT (by simp at hTX; omega)]; simp at hTX; omega
  refine ⟨⟨⟨rfl, (hW s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9).1⟩, Spike.Lib.HelloH2Inv.x2H_off hc ha⟩,
    Spike.Lib.A64.Flow.WakeWc.takeCKS_none (fun _ h => h.1) (fun h => ha (by unfold pcOf; rw [h])) hc⟩

open Spike.Lib.A64.Flow.Worker.Hello.SpawnFail (fNS MSS flB flB_ok flB_run cb_noRet cl_noRet flB_noRet ac_cb ac_cl
  ac_fl hello_failIn failIn) in
open Spike.Lib.A64.Flow.Worker.Hello.Parent (cbP_ok cl_ok cbP_run cbPT_run cl_run clT_run) in
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (ofInt_add8 subs0_lt) in
/-- **`RefO.BlkH` at the third level**: `blk1H` at `cb` (`.sp6 + 4 · 26`), `cl` (`.clone13`) and `flB`
(`.1_spawnfail5`), their runs ending at `.clone13` (the `cbz` not taken), `.1_spawnfail5` (the `b.lt` taken)
and `scc_rt_abort` with `.sp15`'s return address; the source placed from `PreH`'s slice and slots
(`placedSE_blkMSS`). -/
theorem refBlkH {l : WeakMem.AllocLabel} {ws : List TermRun.Word} :
    RefO.BlkH L lbl l ws (fun s c => RootWX.W2H L a ar Spike.Lib.HelloSrc.helloSrc Dt (ClH L) Ctx lbl lsize s c [] ∧
        Spike.Lib.HelloH2Inv.X2H L (L.lab siteL) endX lbl' lsize' s c [])
      (Spike.Lib.A64ConsumerA.TakeCKS (L.lab siteL) (ClH L)) := by
  intro R m0 cP sl cA me hpre
  obtain ⟨hsrc, hsl, hcA, hme, hR, hal, hRlo, hhi, -⟩ := hpre
  have hoff : ∀ k : Int, k % 8 = 0 → -400 ≤ k → k + 8 ≤ 0 → R.Off k := fun k h1 h2 h3 =>
    ⟨h1, by omega, by omega⟩
  have hin := hello_failIn
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hcb, -⟩, hcl⟩, hfl⟩ := hin
  have hF : ∀ X, codeOf lo SccCode.helloProg ".L22_wc_main.sp6" = some X → X + 148 < 2 ^ 63 ∧
      codeOf lo SccCode.helloProg (pfxM ++ ".clone13") = some (X + 108) ∧
      codeOf lo SccCode.helloProg (pfxM ++ ".1_spawnfail5") = some (X + 132) := by
    intro X hX
    obtain ⟨X', hX', h⟩ := of_atLH (Bool.and_eq_true _ _ ▸ blkFactsH_ok).1
    obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hX)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, -⟩ := h
    obtain ⟨y, hy, e⟩ := of_atLH h2
    obtain ⟨z, hz, e'⟩ := of_atLH h3
    simp only [beq_iff_eq] at e e'
    exact ⟨h1, e ▸ hy, e' ▸ hz⟩
  have e6 : (pfxM ++ ".sp6" : String) = ".L22_wc_main.sp6" := rfl
  have hpl := fun (nd : ND) (blk : List Directive) (hJ' : ∀ σ c, nd.J σ c → c = cP ∧ MSS sl cA me σ) hk =>
    placedSE_blkMSS (Λ := L.Λ) (exe := L.exe) (endPc := L.endPc) (F := Spike.Lib.A64.Flow.DFrame R m0)
      (n := nd) (blk := blk) hsrc hsl hcA hme (hoff _ (by decide) (by decide) (by decide))
      (hoff _ (by decide) (by decide) (by decide)) (hoff _ (by decide) (by decide) (by decide))
      (hoff _ (by decide) (by decide) (by decide)) (hoff _ (by decide) (by decide) (by decide)) hJ' hk
  have hJc : ∀ {P : Prop} (c : Spike.Lib.Ctl), c = cP ∧ P →
      (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf Spike.Lib.HelloSrc.helloSrc c [] := by
    rintro P c ⟨rfl, -⟩; exact Spike.Lib.HelloH1A.spawnSrcH_ctl hsrc
  refine ⟨blk1H hp hlo hΛ hlab hsite hR hal (by omega) hhi hcb
    (by simp only [fNS, Spike.Lib.A64.Flow.ofNat4_succ]) cbP_ok (by decide) (cb_noRet _) (refPh_cbH hΛ hlab)
    (Es := []) (by decide +kernel) (fun _ _ _ _ _ h => by simp at h)
    (fun s σ c j m hJ hj hA => ac_cb (cA := cA) (mT := me) s σ c j m
      ⟨hJ.1, hJ.2.1, hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2⟩ hj hA)
    (fun σ c h => hJc c h) (hpl _ _ (fun σ c h => ⟨h.1, h.2.2⟩) (keeps_fNS _ (by simp)))
    0 (by decide) (fun X hX => ⟨X, by rw [e6]; exact hX, by omega⟩) ?_,
    blk1H hp hlo hΛ hlab hsite hR hal (by omega) hhi hcl
    (by simp only [fNS, Spike.Lib.A64.Flow.ofNat4_zero]) cl_ok (by decide) (cl_noRet _) (refPh_clH hΛ hlab)
    (Es := []) (by decide +kernel) (fun _ _ _ _ _ h => by simp at h)
    (fun s σ c j m hJ hj hA => ac_cl (cA := cA) (mT := me) (hoff _ (by decide) (by decide) (by decide)) s σ c j m
      ⟨hJ.1, hJ.2.1, hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2⟩ hj hA)
    (fun σ c h => hJc c h) (hpl _ _ (fun σ c h => ⟨h.1, h.2.2⟩) (keeps_fNS _ (by simp)))
    1 (by decide) (fun X hX => ⟨X + 108, (hF X hX).2.1, by omega⟩) ?_,
    blk1H hp hlo hΛ hlab hsite hR hal (by omega) hhi hfl
    (by simp only [fNS, Spike.Lib.A64.Flow.ofNat4_zero]) flB_ok (by decide) flB_noRet (refPh_flH hΛ hlab)
    (Es := [1]) (by decide +kernel)
    (fun σ c _ j hj h => by
      simp at h; subst h
      show (Spike.Lib.A64.Flow.arun _ flB _).σ.regs.X0 ≠ 4
      rw [fNS, flB_run]; dsimp only; decide)
    (fun s _ _ j m _ hj _ => ac_fl (cP := cP) (cA := cA) (mT := me) s j m hj)
    (fun σ c h => hJc c h) (hpl _ _ (fun σ c h => h) (keeps_fNS _ (by simp)))
    7 (by decide) (fun X hX => ⟨X + 132, (hF X hX).2.2, by omega⟩) ?_⟩
  · intro σ c hJ s m _ hs
    refine .inl fun X hX => ⟨1, by decide, ?_⟩
    have hne : σ.regs.X0.toBitVec ≠ 0#64 := hJ.2.1.ne_zero
    unfold pcOf; rw [hs]; simp only [fNS, cbP_run, cbPT_run, hne, ↓reduceIte]
    show (L.lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 25) + 4 + 4).toBitVec.toNat = _
    rw [hlab _ _ hX, show (4 : Int64) = Int64.ofNat 4 from rfl, ← Int64.ofNat_add, ← Int64.ofNat_add,
      ← Int64.ofNat_add, toNat_ofNat (by have := (hF X hX).1; omega)]
  · intro σ c hJ s m _ hs
    refine .inl fun X hX => ⟨7, by decide, ?_⟩
    have hlt := subs0_lt hJ.2.1.slt
    unfold pcOf; rw [hs]; simp only [fNS, cl_run, clT_run, hlt, ↓reduceIte, Spike.Lib.A64.Flow.rl]
    rw [toNat_labH hlab (hF X hX).2.2 (by have := (hF X hX).1; omega)]
  · intro σ c _ s m hA hs
    simp only [fNS, flB_run] at hA hs
    refine .inr ⟨by unfold pcOf; rw [hs], ?_⟩
    unfold x30At
    rw [show s.st.1 = m by rw [hs], hA.regs]
    exact (ofInt_add8 _).trans (RefO.raT_sp15H hlab)

end Gen

end Spike.Lib.A64.HelloPh.RefBlkH

/-- info: 'Spike.Lib.A64.HelloPh.RefBlkH.dChkAH_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefBlkH.dChkAH_sound

/-- info: 'Spike.Lib.A64.HelloPh.RefBlkH.blk1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefBlkH.blk1H

/-- info: 'Spike.Lib.A64.HelloPh.RefBlkH.refBlkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefBlkH.refBlkH
