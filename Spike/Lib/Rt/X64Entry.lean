/-
**`_start` on x86-64, parametric in the program** (`entry_segW'`): the hand
`Spike.Lib.X64.Flow.Ret0.Inst.entry_segW` (`Spike/Lib/X64Ret0I.lean`) with
the code check `Code.Start.entryIn cells` (`RtCodeIn.start0`,
`Spike/Lib/Rt/X64RtCode.lean`) in place of its `ret0` instance, at any
region `R` with a 16-aligned top and room for `scc_rt_start`'s frames, any
frame condition `F` kept by the outside moves `K`, and `K` keeping `R`'s
cells. The x86-64 twin of `Spike.Lib.A64.Rt.entry_segW'`
(`Spike/Lib/Rt/A64Segs.lean`).

- `_start` is `xorl %ebp, %ebp` (`flag_ndW`), `andq $-16, %rsp`, which keeps
  the region's 16-aligned top (`and16`) and so the region (`swand_ndW`), and
  `call scc_rt_start` (`call_nd_FWK` with `KC := True`), its callee's
  region `R.callee (-8) (-296) 8`. The callee's segment is `hS`, for every
  frame condition stable there, kept by `K` and implying `F`: the shape of
  `x64_start_segW`'s conclusion (`Spike/Lib/LowerX64/StartSeg.lean`).
- The nodes' obligations (`EntryW`) stay premises, as ARM's `hEntry`.
- `entry_segW_take`: at the entry stack (`entryR`), the runtime's entry
  frame condition (`rtF L`) and the take's outside moves (`TakeK a rS`, the
  range in the layout's pool), every side condition discharged.
-/
import Spike.Lib.Rt.X64Segs

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field)

/-- A 16-aligned word is kept by `&&& -16`. -/
theorem and16 {x : BitVec 64} (h : x.toNat % 16 = 0) : x &&& (-16 : Int64).toBitVec = x := by
  have hc : (-16 : Int64).toBitVec = ~~~15#64 := by decide
  have h15 : x &&& 15#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h
  rw [hc]
  generalize (15#64) = y at h15 ⊢
  ext i hi
  have := congrArg (fun z => z[i]) h15
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero] at this ⊢
  cases hx : x[i] <;> simp_all

section Nodes

variable (lab : Label → Int64) (c0 : Ctl)

/-- **`_start`'s entry node**: at `_start`, at its region's top (offset
`0`), the source at `c0` (the hand `entry0N` at `lab`). -/
def entryN0 : ND := ⟨lab "_start", ⟨0, []⟩, fun _ c => c = c0⟩
/-- After `_start`'s `xorl %ebp, %ebp`. -/
def entryN1 : ND := ⟨lab "_start" + Int64.ofNat 2, ⟨0, []⟩, fun _ c => c = c0⟩
/-- After `_start`'s `andq $-16, %rsp`, at the call, in a fresh region. -/
def entryN2 : ND := ⟨lab "_start" + Int64.ofNat 2 + Int64.ofNat 4, SO.entry, fun _ c => c = c0⟩
/-- At `scc_rt_start` as seen from `_start`'s call: the return address at
offset `-8` of the region. -/
def entryNC : ND := ⟨lab "scc_rt_start", ⟨-8, []⟩, fun _ c => c = c0⟩

end Nodes

block_spec entryCallB (-8) 0 SO.entry Code.Start.entryCall

/-- **`_start`'s nodes' obligations inside `W`**: the `xorl`'s and the
`andq`'s nodes, and the call's block. -/
structure EntryW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (lab : Label → Int64) (c0 : Ctl) : Prop where
  xor : NodeW W K exe endPc R F (entryN0 lab c0)
  and : NodeW W K exe endPc R F (entryN1 lab c0)
  call : BlkW W K exe endPc R F (entryN2 lab c0) Code.Start.entryCall

/-- `EntryW` in a larger `W`. -/
theorem EntryW.mono {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {lab : Label → Int64} {c0 : Ctl} (h : EntryW W K exe endPc R F lab c0)
    (hW : ∀ s c, W s c → W' s c) : EntryW W' K exe endPc R F lab c0 where
  xor s c hA := ⟨hW _ _ (h.xor s c hA).1, (h.xor s c hA).2⟩
  and s c hA := ⟨hW _ _ (h.and s c hA).1, (h.and s c hA).2⟩
  call s σ c hs hn hd hpc hA hD hJ k hk m hA' hD' :=
    ⟨hW _ _ (h.call s σ c hs hn hd hpc hA hD hJ k hk m hA' hD').1,
      (h.call s σ c hs hn hd hpc hA hD hJ k hk m hA' hD').2⟩

section EntryProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`_start` as one segment inside `W`** (hand `entry_segW`), in any valid
layout of any cells with `_start`'s code (`hin`): `xorl %ebp, %ebp`,
`andq $-16, %rsp` (the region's top 16-aligned, `hal`), and the call of
`scc_rt_start`, its callee's region `R.callee (-8) (-296) 8`; `K` keeps `F`
(`hFK`) and `R`'s cells (`hKR`). The callee's segment is `hS`, for every
frame condition `F'` stable in the callee's region, kept by `K` and
implying `F`. -/
theorem entry_segW' {W : Frag isa} {K : State → State → Prop} (hp : Lays exe cells)
    (hend : endPc = endOf exe cells) (hin : Code.Start.entryIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -8 + -296) (hhi : 0 ≤ R.hi)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (c0 : Ctl) (hW : EntryW W K exe endPc R F (_root_.Executable.labels exe).label c0) {Q : Frag isa}
    (hS : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' → KStable K F' →
      (∀ m, F' m → F m) → ∀ Q' : Frag isa,
      SegW W K p lbl ms
        (At exe endPc (R.callee (-8) (-296) 8) F' (startN0 (_root_.Executable.labels exe).label c0)) Q') :
    SegW W K p lbl ms (At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [Code.Start.entryIn, Bool.and_eq_true] at hin
  obtain ⟨⟨hb0, hb1⟩, hb2⟩ := hin
  refine (seg_oneW (flag_ndW (n := entryN0 lab c0) (N := fun _ : Unit => entryN1 lab c0)
    (E := fun e : Empty => e.elim) (fi := .xor_rr32_self .rbp) (z := 2) rfl hF
    (code_field hp hend hb0 (ofNat_zero' _)) hW.xor
    fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(), rfl, rfl, hJ⟩⟩)).seq ?_
  refine sw_seqW (lo := R.lo) (hi := R.hi) (F' := fun v m => v = R.base ∧ F m) (n' := entryN2 lab c0)
    (swand_ndW (k := -16) (z := 4) (n := entryN1 lab c0) (code_field hp hend hb1 rfl) rfl rfl hW.and
      fun m σ c hA hD hJ fl => ?_) fun v _ => ?_
  · have hsp : σ.regs.get64 .rsp = R.base := by
      rw [hA.so .rsp 0 rfl]; simp [Region.addr]
    have hv : (andRegs (-16) σ.regs).get64 .rsp = R.base := by
      simp only [andRegs, Reg64s.get64_set64_self]; rw [hsp]; exact and16 hal
    rw [hv]
    exact ⟨hR, ⟨rfl, hF _ _ hD fun _ _ _ => rfl⟩, σ.slot, fun k hk => hA.slot k hk, c, .refl c, hJ⟩
  refine SegW.mono_pre (P := At exe endPc R F (entryN2 lab c0)) ?_
    fun s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hvb, hD⟩, hJ⟩ => ⟨he, hn, hdc, hpc, σ, by subst hvb; exact hA, hD, hJ⟩
  refine (seg_oneW (seg_ndW (N := fun _ : Unit => entryNC lab c0) (E := fun e : Empty => e.elim)
    (by simp [Code.Start.entryCall]) entryCallB_ok hF hR (by omega) (by omega)
    (code_field hp hend hb2 (ofNat_add' _ 2 4)) hW.call
    fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).seq ?_
  · rw [show (entryN2 lab c0).o = SO.entry from rfl, entryCallB_run]; rfl
  · rw [show (entryN2 lab c0).o = SO.entry from rfl, entryCallB_run]; rfl
  · exact hJ
  refine (call_nd_FWK (KC := True) (nC := entryNC lab c0) (exe := exe) (endPc := endPc)
    (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0) (lo' := -296) (hi' := 8)
    (M := fun _ => True) (F₂ := F)
    (Ne := fun _ : Unit => startN0 lab c0) (Ex := fun _ (e : Empty) => e.elim)
    hR hF (by show R.lo ≤ -8 - 0 + -296; omega) (by decide)
    (by show (-8 : Int) - 0 < R.hi; omega) (by show (-8 : Int) - 0 + 8 ≤ R.hi; omega)
    (by show ((-8 : Int) - 0) % 8 = 0; decide) (by decide) (by decide)
    (fun _ => hFK)
    (fun _ s s' hk hFs k hk' _ => hKR s s' hk hFs k hk')
    (fun _ h _ => h)
    (fun R' F' _ _ _ hF' hK' hFF hR'e _ _ _ _ => by subst hR'e; exact hS F' hF' (hK' trivial) hFF _)
    (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ⟩) fun _ x => x.elim).mono_post
    fun _ _ h => h.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim

end EntryProof

section Take

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}

/-- **`_start` at the runtime's layout `L`** (`entry_segW'` at `L`'s cells,
the entry stack `entryR E` of an admissible `E` (`hE`), the entry frame condition `rtF L` and the take's
outside moves `TakeK a rS`, `rS` in `L`'s pool): the side conditions by
`rtF_stable`, `entryR_ok`, `entryR_al`, `rtF_takeMem` and `rS_of_sub`. -/
theorem entry_segW_take (L : RuntimeLayout) {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {W : Frag isa} {a : Int64}
    {rS : Scc.Sem.Range} (hin : Code.Start.entryIn L.prog = true) (hsub : rS.Sub L.pool) (c0 : Ctl)
    (hW : EntryW W (TakeK a rS) L.exe L.endPc (entryR E) (rtF L) L.lab c0) {Q : Frag isa}
    (hS : ∀ F' : MachineData → Prop, FStable ((entryR E).callee (-8) (-296) 8) F' → KStable (TakeK a rS) F' →
      (∀ m, F' m → rtF L m) → ∀ Q' : Frag isa,
      SegW W (TakeK a rS) p lbl ms (At L.exe L.endPc ((entryR E).callee (-8) (-296) 8) F' (startN0 L.lab c0)) Q') :
    SegW W (TakeK a rS) p lbl ms (At L.exe L.endPc (entryR E) (rtF L) (entryN0 L.lab c0)) Q :=
  entry_segW' L.lays rfl hin (rtF_stable L hE) (entryR_ok hE) (entryR_al hE)
    (by show (-65536 : Int) ≤ -8 + -296; decide) (by show (0 : Int) ≤ 0; decide)
    (TakeK.kstable fun _ _ h => rtF_takeMem L hsub h)
    (fun _ _ hk _ k hk' => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (rS_of_sub L hE hsub k hk'))
    c0 hW hS

end Take

end Spike.Lib.X64.Rt
