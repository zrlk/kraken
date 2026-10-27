/-
**The x86-64 runtime's segments with `scc_rt_thread_init`'s return point at
any label** (`Spike/Lib/Rt/X64Segs.lean` at `x`): x86-64 numbers the `.x`
labels per program, so `scc_rt_thread_init` returns to `.x7` after a bare
`scc_rt_main` and to `.x8` after a setup block
(`Spike.Lib.X64.Rt.tiOf`). The segments here take the code check
`threadInitInAt cells x` and the obligations `TiWAt … x`, `X0WAt … x`,
`StartAllUWAt … x` (`Spike/Lib/Rt/X64RtTi.lean`,
`Spike/Lib/Rt/X64RtStartU.lean`), which `startAllUWAt_gen` discharges at
`tiOf o.place.tail` for any placed output.

- `threadInit_segWAt`, `startX0Sw_segWAt`, `startU_segWAt`: the proofs of
  `threadInit_segW`, `startX0Sw_segW`, `startU_segW` with `.x7` replaced by
  `x` (the nodes `tiNGAt`, from `tiNAt`).
- At `.x7` they give the originals' statements (`threadInit_segW_ofAt`,
  `startX0Sw_segW_ofAt`, `startU_segW_ofAt`, by `tiWAt_x7`, `X0W.toAt`,
  `StartAllUW.toAt`).
- **TODO**: the three proofs (about 330 lines) duplicate `X64Segs`'s; once
  `TiWAt`/`X0WAt` move upstream of `X64Segs`, the original lemmas can be
  derived from these and the copies dropped.
-/
import Spike.Lib.Rt.X64Segs
import Spike.Lib.Rt.X64RtStartU

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The nodes with the take's ghost at any return point -/

section NodesAt

variable (lab : Label → Int64) (q : TiG) (x : Label)

/-- **`tiNG` with the return point at `x`**: `tiNAt`, the nodes after the
call of `scc_rt_stack_take` only once the take is done (`b`). -/
def tiNGAt (b : Bool) : TI → ND
  | .e => tiNAt lab q x .e
  | .entry => tiNAt lab q x .entry
  | .c7 => tiNAt lab q x .c7
  | .call => tiNAt lab q x .call
  | .x7 => tiA b (tiNAt lab q x .x7)
  | .st0 => tiA b (tiNAt lab q x .st0)
  | .f1 => tiA b (tiNAt lab q x .f1)
  | .st1 => tiA b (tiNAt lab q x .st1)
  | .f2 => tiA b (tiNAt lab q x .f2)
  | .st2 => tiA b (tiNAt lab q x .st2)
  | .f3 => tiA b (tiNAt lab q x .f3)
  | .st3 => tiA b (tiNAt lab q x .st3)
  | .f4 => tiA b (tiNAt lab q x .f4)
  | .st4 => tiA b (tiNAt lab q x .st4)
  | .f5 => tiA b (tiNAt lab q x .f5)
  | .st5 => tiA b (tiNAt lab q x .st5)
  | .ret => tiA b (tiNAt lab q x .ret)

theorem tiNGAt_x7 (b : Bool) : tiNGAt lab q ThreadInit.x7L b = tiNG lab q b := by
  funext i; cases i <;> rfl

end NodesAt

/-- `TiWAt` under a stronger frame condition (`TiW.mono` at any return point). -/
theorem TiWAt.mono {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {W : Frag isa} {K : State → State → Prop} {F' M : MachineData → Prop} {q : TiG} {x : Label} {i : TI}
    (h : TiWAt W K exe endPc R F M q x i) (hFF : ∀ m, F' m → F m) : TiWAt W K exe endPc R F' M q x i := by
  cases i <;> dsimp only [TiWAt] at h ⊢
  all_goals first
    | exact blkW_mono h hFF
    | exact nodeW_mono h hFF
    | exact blkW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact nodeW_mono h fun m h => ⟨hFF m h.1, h.2⟩
    | exact fun g hg i => (h g hg i).mono hFF

/-! ## `scc_rt_thread_init` -/

section TiWProofAt

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_init` inside `W`. -/
local macro "inodeWA " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR (by omega) hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at the store of field `i` (`8·i(%rcx)`, `z` bytes) at `x + k`,
to node `j`, inside `W`, after the take. -/
local macro "snodeWA " i:term:max d:term:max k:term:max z:term:max v:term:max j:term:max w:term:max : tactic =>
  `(tactic| (
    refine rtst_ndW (b := .rcx) (k := $d) (r := .rax) (z := $z)
      (code_field hp hend (by simp only [hin']) (l := xr) (off := $k) rfl) $w
      fun m σ c _ hD hJ => ?_
    dsimp only [tiNGAt, tiA, tiNAt] at hJ
    obtain ⟨rfl, rfl, hJ, ha, hc⟩ := hJ
    have hfi := hfld (8 * $i, $v) (by simp [ThreadInit.fields])
    rw [bAddr_rcx hc, show BitVec.ofInt 64 (Int64.toInt $d) = BitVec.ofNat 64 (8 * $i) by decide,
      show σ.regs.get64 .rax = σ.regs.rax.toBitVec from rfl, ha]
    exact ⟨hfi.rt, hfi.mp, hfi.G, hfi.unmapped m (hFFb m hD), q.c0,
      .refl q.c0, .inl ⟨$j, ofNat_add' _ $k $z, rfl, rfl, rfl, hJ⟩⟩))

/-- **`scc_rt_thread_init` is one segment inside `W`, the take its outside
move**: `thread_init_seg` with `stackTake_segW` at the call, so at the
return the stack range `rS` is in private memory (`StackM`). Given the node
obligations (`hW`), the region's cells off `rS` (`hRS`), every aligned word
of `rS` off the region (`hout`), and the frame condition kept by the take
(`hFt`). -/
theorem threadInit_segWAt {xr : Label} {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : ThreadInit.threadInitInAt cells xr = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiWAt W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      xr i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [ThreadInit.threadInitInAt, ThreadInit.storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_left,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := ThreadInit.fnL) (b := ThreadInit.entryL) (off := 12) hp (by simp only [hin'])
  have eX7 := label_labelGapB (a := ThreadInit.entryL) (b := xr) (off := 12) hp (by simp only [hin'])
  have hcall : blockAtB cells ThreadInit.entryL 7 tiCall = true :=
    (by simp only [hin'] : blockAtB cells ThreadInit.entryL 7 ThreadInit.callBlk = true)
  let lab := (_root_.Executable.labels exe).label
  have hSM := stackM_stable hfit hout
  -- the take's callee region, and `rS` off it
  have hb' := Region.callee_base (hi' := 8) hR (show R.lo ≤ (-48 - 0) + -200 by omega) (by decide)
    (show (-48 - 0 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48 - 0) (-200) 8).Off k → ∀ i < 8,
      (R.callee (-48 - 0) (-200) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ (-48 - 0) + -200 by omega) (show (-48 - 0 : Int) + 8 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48 - 0) (-200) 8).base.toNat + (R.callee (-48 - 0) (-200) 8).lo ∨
        ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + (R.callee (-48 - 0) (-200) 8).hi ≤ a :=
    fun a h8 ha ha7 => by
      show (a : Int) + 8 ≤ ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + -200 ∨
        ((R.callee (-48 - 0) (-200) 8).base.toNat : Int) + 8 ≤ a
      rcases hout a h8 ha ha7 with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R) (Fg := takeF F rS)
      (N := tiNGAt (_root_.Executable.labels exe).label q xr) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, nofun⟩, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFb : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m → F0 m := fun m h => hFF m h.1
  cases i
  case e =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0 (blkW_mono (hW TI.e) fun m h => h.1)
    dsimp only [tiNGAt, tiNAt] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiArg ThreadInit.tiArg_ok ThreadInit.entryL 0 (blkW_mono (hW TI.entry) fun m h => h.1)
    dsimp only [tiNGAt, tiNAt] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := ThreadInit.tiArg_walk lab _ hJ
    exact .inl ⟨TI.c7, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4⟩
  case c7 =>
    refine seg_fixW b ?_
    refine seg_ndW (by simp [tiCall]) tiCall_ok hFb hR (by omega) hhi
      (code_field hp hend hcall rfl) (blkW_mono (hW TI.c7) fun m h => h.1) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNGAt, tiNAt] at hJ ⊢
    obtain ⟨rfl, ⟨hsp, hfp, hs⟩, hdi⟩ := hJ
    rw [tiCall_run]
    refine .inl ⟨TI.call, rfl, rfl, ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p hp'
      have hp48 : p.1 ≠ -48 := by
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl <;> simp
      simp only [upd_apply, hp48, ↓reduceIte]
      exact hs p hp'
    · simp [Reg64s.set64, hsp]; bv_omega
    · simp [Reg64s.set64, hfp]
    · simp [Reg64s.set64, hdi]
    · simp only [upd_apply, ↓reduceIte]
      rw [eX7, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]; rfl
  case call =>
    refine seg_fixW true ?_
    refine call_nd_FW (e0 := 0) (lo' := -200) (hi' := 8) (M := StackM rS)
      (Ne := fun g => takeNG lab (tiTake q g) false .e) (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hFb (by show R.lo ≤ -48 - 0 + -200; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h.1, fun _ => hM⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab xr).toBitVec := by
          have e : lab xr = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (stackTake_segW hp hend hst hF' hR' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk htk
          (fun i => (hW TI.call g' hr i).mono fun m h => (hFF' m h).1) hRS' hfit hout'
          (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, -, -, -, h0⟩, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, hs, hsp, hfp, -⟩, h48⟩ ⟨-, hsp', hfp', hra', -⟩ ⟨-, rfl, hPost⟩ hregs - - hslot
      have hk' : ∀ k : Int, k % 8 = 0 → R.lo ≤ k → k + 8 ≤ R.hi → -48 < k → σR.slot k = σC.slot k :=
        fun k h1 h2 h3 h4 => hslot k ⟨h1, h2, h3⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [tiNGAt, tiNAt] at h; omega
      refine .inl ⟨TI.x7, ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, rfl, rfl, ⟨?_, ?_, ?_⟩,
        ?_⟩
      · show lab xr = Int64.ofBitVec g.ra
        rw [← hra']
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · show σR.regs.rsp.toBitVec = _
        rw [hregs, hPost.1, ← hsp']
        show σC.regs.rsp.toBitVec + 8#64 = _
        rw [hsp]; bv_omega
      · show σR.regs.rbp.toBitVec = _
        rw [hregs, hPost.2.1, ← hfp']
        exact hfp
      · intro p hp'
        simp only [ThreadInit.s0, List.mem_cons, List.mem_nil_iff, or_false] at hp'
        rcases hp' with rfl | rfl | rfl
        · rw [hk' 0 (by decide) (by omega) (by omega) (by decide)]; exact hs (0, q.g.ra) (by simp)
        · rw [hk' (-8) (by decide) (by omega) (by omega) (by decide)]; exact hs (-8, q.g.fp) (by simp)
        · rw [hk' (-16) (by decide) (by omega) (by omega) (by decide)]; exact hs (-16, q.tcb) (by simp)
      · show σR.regs.rax.toBitVec = _
        rw [hregs]; exact hPost.2.2
  case x7 =>
    refine seg_fixW b ?_
    refine SegW.mono_pre (P := At exe endPc R (takeF F rS b) (tiA b (tiX7At lab q xr))) ?_
      fun _ _ h => At.rbp h fun σ c ⟨_, _, ⟨hsp, hfp, _⟩, _⟩ => by
        simp only [Reg64s.get64]; rw [hsp, hfp]; bv_omega
    refine seg_ndW (by simp [ThreadInit.tiSp]) ThreadInit.tiSp_ok hFb hR (by omega) hhi
      (code_field hp hend (by simp only [hin']) (l := xr) (off := 0) (ofNat_zero' _))
      (blkW_tiS (hW TI.x7)) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNGAt, tiA, tiX7At, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ ha
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    snodeWA 0 0 48 3 q.tcb TI.f1 (nodeW_tiS (hW TI.st0))
  case f1 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF1 ThreadInit.tiF1_ok xr 51 (blkW_tiS (hW TI.f1))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1]; exact ofNat_add' _ 51 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    snodeWA 1 8 59 4 (tiBase (_root_.Executable.labels exe).label q + 4096#64) TI.f2
      (nodeW_tiS (hW TI.st1))
  case f2 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiZ ThreadInit.tiZ_ok xr 63 (blkW_tiS (hW TI.f2))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1]; exact ofNat_add' _ 63 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    snodeWA 2 16 74 4 (0#64) TI.f3 (nodeW_tiS (hW TI.st2))
  case f3 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiZ ThreadInit.tiZ_ok xr 78 (blkW_tiS (hW TI.f3))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1]; exact ofNat_add' _ 78 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    snodeWA 3 24 89 4 (0#64) TI.f4 (nodeW_tiS (hW TI.st3))
  case f4 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF4 ThreadInit.tiF4_ok xr 93 (blkW_tiS (hW TI.f4))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1]; exact ofNat_add' _ 93 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    snodeWA 4 32 101 4 (tiBase (_root_.Executable.labels exe).label q) TI.f5
      (nodeW_tiS (hW TI.st4))
  case f5 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF5 ThreadInit.tiF5_ok xr 105 (blkW_tiS (hW TI.f5))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1]; exact ofNat_add' _ 105 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    snodeWA 5 40 113 4 (tiBase (_root_.Executable.labels exe).label q + 16384#64) TI.ret
      (nodeW_tiS (hW TI.st5))
  case ret =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiRet ThreadInit.tiRet_ok xr 117 (blkW_tiS (hW TI.ret))
    dsimp only [tiNGAt, tiA, tiNAt, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩

end TiWProofAt

/-! ## `scc_rt_start` up to the switch -/

section StartProofAt

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

/-- **`scc_rt_start` from `.x0` to the switch, inside `W`, the take its
outside move** (`start_x0_x1_seg` then `start_x1_sw_seg`, their states'
obligations `hW`, with `thread_init_segW` at the call): from `.x1` on the
stack range `rS` is in private memory (`StackM`). Given the take's facts at
the region (`hRS`, `hfit`, `hout`, `hFt`). -/
theorem startX0Sw_segWAt {xr : Label} {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitInAt cells xr = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : X0WAt W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0 xr)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) := by
  let lab := (_root_.Executable.labels exe).label
  let tcb := pinA lab + n0 + 8#64
  simp only [startCall2In, Bool.and_eq_true] at hin
  have ex1 := label_labelGapB hp hin.2
  have hSM := stackM_stable hfit hout
  have hF2 : FStable R (fun m => F m ∧ StackM rS m) := fun m m' h hd => ⟨hF m m' h.1 hd, hSM m m' h.2 hd⟩
  -- `scc_rt_thread_init`'s region, and `rS` off it
  have hb' := Region.callee_base (hi' := 8) hR (show R.lo ≤ (-48 - 0) + -248 by omega) (by decide)
    (show (-48 - 0 : Int) < R.hi by omega)
  have hRS' : ∀ k, (R.callee (-48 - 0) (-248) 8).Off k → ∀ i < 8,
      (R.callee (-48 - 0) (-248) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off (show R.lo ≤ (-48 - 0) + -248 by omega) (show (-48 - 0 : Int) + 8 ≤ R.hi by omega)
      (by decide) hk) i hi
  have hout' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-48 - 0) (-248) 8).base.toNat + (R.callee (-48 - 0) (-248) 8).lo ∨
        ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + (R.callee (-48 - 0) (-248) 8).hi ≤ a :=
    fun a h8 ha ha7 => by
      show (a : Int) + 8 ≤ ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + -248 ∨
        ((R.callee (-48 - 0) (-248) 8).base.toNat : Int) + 8 ≤ a
      rcases hout a h8 ha ha7 with h | h
      · exact .inl (by omega)
      · exact .inr (by omega)
  refine SegW.seq (Q := At exe endPc R F (startNC2 lab tcb c0)) ?_
    (SegW.seq (Q := At exe endPc R (fun m => F m ∧ StackM rS m) (startN3 lab n0 k0 c0))
      ((seg_oneW (n := ⟨lab x1L, ⟨-40, []⟩, (startN3 lab n0 k0 c0).J⟩) ?_).mono_post
        fun _ _ h => At.rbp h fun _ _ h => h.2)
      (startX1Sw_segW hp hend htail hK hF2 hR (by omega) (by omega) n0 k0 c0 hW.fs hW.sys hW.sw))
  · -- the call's block
    refine (seg_oneW (seg_ndW (n := startN2R lab n0 c0) (by simp [startCall2]) startCall2_ok hF hR (by omega)
      (by omega) (code_field hp hend hin.1 (ofNat_zero' _)) hW.b0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp_get rfl h
    · dsimp only [startN2R, startN2, startNC2]; rw [startCall2_run]
    · dsimp only [startN2R, startN2, startNC2]; rw [startCall2_run]; rfl
    · dsimp only [startN2R, startN2, startNC2] at hJ ⊢; rw [startCall2_run]
      obtain ⟨⟨⟨rfl, hax⟩, -⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp [Reg64s.set64, Reg64s.get64, upd_apply, hax]; rfl
      · simp only [upd_apply, ↓reduceIte]
        rw [show lab x1L = _ from ex1, Int64.toBitVec_add]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]; bv_omega
  · -- `scc_rt_thread_init`
    refine call_nd_FW (e0 := 0) (lo' := -248) (hi' := 8) (M := StackM rS)
      (Ne := fun g => tiN lab ⟨g, tcb, k0, c0⟩ .e) (Ex := fun g => tiX lab ⟨g, tcb, k0, c0⟩)
      hR hF (by show R.lo ≤ -48 - 0 + -248; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (TakeK.kstable hFt)
      (fun s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨h, hM⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e _ g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48, -⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab x1L).toBitVec := by
          have e : lab x1L = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (threadInit_segWAt hp hend hti hst hF' hR' hlo' hhi' hFF' ⟨g', tcb, k0, c0⟩ hk hfld htk
          (fun i => (hW.ti g' hr i).mono hFF') hRS' hfit hout' (takeMem_of_kstable hK' exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c ⟨⟨rfl, h0, -⟩, -, -⟩
      exact ⟨⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-48 - 0 + 0)⟩, rfl, rfl, rfl, rfl, rfl, h0⟩
    · rintro g x σC c σx c' σR ⟨⟨-, -, h32⟩, h48, hb⟩ ⟨-, hsp, hfp, hra, -⟩ ⟨rfl, hsp', hb', hrax⟩ hregs - - hslot
      refine .inl ⟨(), ?_, by show SO.le ⟨-40, []⟩ ⟨-48 - 0 + 8, []⟩ = true; decide, ⟨rfl, ?_, ?_⟩, ?_⟩
      · show lab x1L = Int64.ofBitVec g.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
        rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hrax
      · rw [hslot (-32) ⟨by decide, by omega, by omega⟩ fun h => by
          simp only [Region.Off, Region.callee] at h; dsimp only [startNC2] at h; omega]
        exact h32
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - -40)
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        rw [hb', hsp', ← hfp, ← hsp]
        show σC.regs.rbp.toBitVec = σC.regs.rsp.toBitVec + 8#64 + BitVec.ofInt 64 (-8 - -40)
        rw [hb]; bv_omega

end StartProofAt

/-! ## `scc_rt_start` whole -/

section StartUAt

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

/-- **`scc_rt_start` never returns, inside `W`, the take its outside move,
`scc_rt_main` parametric** (hand `start_segW`): `startX0_segW`, then
`startX0Sw_segW`, then `startSwitchU_segW`, in any valid layout of any
cells with the runtime's code checks and `scc_rt_main`'s (`hmain`). -/
theorem startU_segWAt {xr : Label} {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hcall : startCallIn cells = true) (hstart : startIn cells = true)
    (hat : AllocTcb.allocTcbIn cells = true) (hcall2 : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitInAt cells xr = true)
    (hst : StackTake.stackTakeIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hkm : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllUWAt W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F ms rS
      n0 k0 c0 L mc D ZU Post xr)
    {Q : Frag isa} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (startX0_segW hp hend hcall hstart hat hK hF hR (by omega) (by omega) n0 c0 hn hhdr htcb hW.s1).seq
    ((startX0Sw_segWAt hp hend hcall2 htail hti hst hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS
      hFt).seq
      (startSwitchU_segW hp hend htail hmain hZ hZ8 hps hkm hD0 hD8 hL hL8 hK _ _ c0 hok (fun _ h => h.2) hfitS
        hsub hfit hout (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit hW.s3))

end StartUAt

/-! ## The originals at `.x7` -/

section OfAt

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

/-- `threadInit_segW`'s statement, from `threadInit_segWAt` at `.x7`. -/
theorem threadInit_segW_ofAt {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F0 exe endPc q.k0)
    (hW : ∀ i, TiW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x,
        At exe endPc R (fun m => F m ∧ StackM rS m) (tiX (_root_.Executable.labels exe).label q x) s c) :=
  threadInit_segWAt (xr := ThreadInit.x7L) hp hend hin hst hF hR hlo hhi hFF q hk hfld htk
    (fun i => by rw [tiWAt_x7]; exact hW i) hRS hfit hout hFt

/-- `startX0Sw_segW`'s statement, from `startX0Sw_segWAt` at `.x7`. -/
theorem startX0Sw_segW_ofAt {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (n0 k0 : BitVec 64) (c0 : Ctl) (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hW : X0W W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN2 (_root_.Executable.labels exe).label n0 c0))
      (At exe endPc R (fun m => F m ∧ StackM rS m) (startN6 (_root_.Executable.labels exe).label
        (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)) :=
  startX0Sw_segWAt (xr := ThreadInit.x7L) hp hend hin htail hti hst hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW.toAt hRS
    hfit hout hFt

/-- `startU_segW`'s statement, from `startU_segWAt` at `.x7`. -/
theorem startU_segW_ofAt {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hcall : startCallIn cells = true) (hstart : startIn cells = true)
    (hat : AllocTcb.allocTcbIn cells = true) (hcall2 : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hkm : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllUW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F ms rS
      n0 k0 c0 L mc D ZU Post)
    {Q : Frag isa} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  startU_segWAt (xr := ThreadInit.x7L) hp hend hcall hstart hat hcall2 htail hti hst hmain hZ hZ8 hps hkm hD0 hD8 hL hL8
    hK hF hR hlo hhi n0 k0 c0 hn hk hhdr htcb hfld htk hok hsub hfit hout hlimM hlimU hexit hRS hfitS houtS hFt
    hW.toAt

end OfAt

end Spike.Lib.X64.Rt
