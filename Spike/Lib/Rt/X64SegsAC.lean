/-
**`scc_rt_thread_init`'s segment with the take's caller cells at its site**
(x86-64): `threadInit_segWAtA` (`Spike/Lib/Rt/X64SegsA.lean`) with the
obligations' take-site condition `P ∧ CallerCells R (-48) (-200) 8`. At the
take's call `call_nd_FWP` hands the callee its caller's cells off the
callee's region (`hcallee`); `threadInit_segWAtA` drops that fact, which
wake's second thread-init call needs at the take site (main's stack owned,
`Ti2.owned_r0_64`). `CallerCells` is not stable under the take's frames,
so it cannot sit in `P` (`FStable`); it rides in the take's frame
condition and is moved into the site condition by `TakeWP.shift`.

- `TakeWP.shift`: part of the site condition moved to the frame;
- `threadInit_segWAtAC`: the segment; its proof is `threadInit_segWAtA`'s
  but for the call's obligation.

**Unlike AArch64**: AArch64's `TiW … P` carries the take's `CallerCells` in
its `.call` field (`threadInit_segWA`); x86-64's `TiWAtP` has `F` alone
there, so the variant asks it at the take site.
-/
import Spike.Lib.Rt.X64SegsA

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false


/-- **`TakeWP` with part `Q` of the site condition moved to the frame**:
under a frame `F'` that gives both `F` and `Q`, the site's `P ∧ Q` asks
`P` alone. -/
theorem TakeWP.shift {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F F' M P Q : MachineData → Prop} {q : TakeG} {i : TK}
    (h : TakeWP W K exe endPc R F M q (fun m => P m ∧ Q m) i) (hFF : ∀ m, F' m → F m ∧ Q m) :
    TakeWP W K exe endPc R F' M q P i := by
  by_cases hi : i = .site
  · subst hi
    exact fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ =>
      h s c ⟨he, hn, hdc, hpc, σ, hA, ⟨(hFF _ hD.1).1, hD.2, (hFF _ hD.1).2⟩, hJ⟩
  · rw [takeWP_eq hi] at h ⊢
    exact h.mono fun m hm => (hFF m hm).1

section TiWProofAtAC

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
/-- `inodeWA` for a block split by its return label `r` after `n` rows
(`blockAcrossB`, `Spike.Lib.X64.code_field_blockAcrossB`). -/
local macro "inodeWX " b:ident ok:ident l:term:max k:term:max n:term:max r:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hFb hR (by omega) hhi
    (Spike.Lib.X64.code_field_blockAcrossB hp hend (by simp only [hin']) (l := $l) (m := $r) (off := $k)
      (List.take_append_drop $n _) (by first | rfl | exact ofNat_zero' _))
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

/-- **`threadInit_segWAtA` with the take's caller cells at its site**: as
`threadInit_segWAtA`, the obligations' take-site condition
`P ∧ CallerCells R (-48) (-200) 8` (the caller's cells off the take's
region): the call's `call_nd_FWP` gives the take's frames those cells
(`hcallee`), moved off the site condition into the frame by
`TakeWP.shift`; only `P` must be `FStable`. -/
theorem threadInit_segWAtAC {xr : Label} {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : ThreadInit.threadInitInAt cells xr = true)
    (hst : StackTake.stackTakeIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TiG) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields q.tcb (tiBase (_root_.Executable.labels exe).label q),
      StOk ms F0 (q.tcb + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, TakeOkA ms F0 exe endPc (R.callee (-48 - 0) (-200) 8) F (tiTake q g))
    {P : MachineData → Prop} (hP : FStable R P)
    (hW : ∀ i, TiWAtP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F (StackM rS) q
      xr (fun m => P m ∧ CallerCells R (-48 - 0) (-200) 8 m) i)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (fun s c => At exe endPc R F (tiN (_root_.Executable.labels exe).label q .e) s c ∧ P s.st.1)
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
  -- `P` held until the take's call (`b = false`); the nodes up to it gated by `b = false` (`tiNPAt`)
  refine ((fn_seg_gW (exe := exe) (endPc := endPc) (Rg := fun _ => R)
      (Fg := fun b m => takeF F rS b m ∧ (b = false → P m))
      (N := tiNPAt (_root_.Executable.labels exe).label q xr) (E := tiXG (_root_.Executable.labels exe).label q)
      (fun b i => ?_) false TI.e).mono_pre fun s c h => ?_).mono_post
    fun s c h => ?_
  rotate_left
  · obtain ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hPs⟩ := h
    exact ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, nofun⟩, fun _ => hPs⟩, rfl, hJ⟩
  · obtain ⟨g, x, he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hM⟩, -⟩, hb, hJ⟩ := h
    subst hb
    exact ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM rfl⟩, hJ⟩
  have hFt0 : FStable R (takeF F rS b) := fun m m' ⟨hD, hM⟩ hd => ⟨hF m m' hD hd, fun hb => hSM m m' (hM hb) hd⟩
  have hFb : FStable R (fun m => takeF F rS b m ∧ (b = false → P m)) := fun m m' ⟨hD, hPm⟩ hd =>
    ⟨hFt0 m m' hD hd, fun hb => hP m m' (hPm hb) hd⟩
  have hFFb : ∀ m, takeF F rS b m ∧ (b = false → P m) → F0 m := fun m h => hFF m h.1.1
  have hWt : ∀ i, i ≠ TI.call → TiWAt W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F (StackM rS) q xr i := fun i hi => tiWAtP_eq hi ▸ hW i
  cases i <;> dsimp only [tiNPAt]
  case e =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    inodeWA ThreadInit.tiPro ThreadInit.tiPro_ok ThreadInit.fnL 0
      (fun s σ c he hn hdc hpc hA hD hJ => hWt TI.e nofun s σ c he hn hdc hpc hA hD.1.1 hJ.2)
    dsimp only [tiNPAt, tiB, tiNAt] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiPro_walk lab _ hJ
    exact .inl ⟨TI.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, rfl, h3⟩
  case entry =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    inodeWA ThreadInit.tiArg ThreadInit.tiArg_ok ThreadInit.entryL 0
      (fun s σ c he hn hdc hpc hA hD hJ => hWt TI.entry nofun s σ c he hn hdc hpc hA hD.1.1 hJ.2)
    dsimp only [tiNPAt, tiB, tiNAt] at hJ ⊢
    obtain ⟨-, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := ThreadInit.tiArg_walk lab _ hJ
    exact .inl ⟨TI.c7, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4⟩
  case c7 =>
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW false ?_
    refine seg_ndW (by simp [tiCall]) tiCall_ok hFb hR (by omega) hhi
      (code_field hp hend hcall rfl)
      (fun s σ c he hn hdc hpc hA hD hJ => hWt TI.c7 nofun s σ c he hn hdc hpc hA hD.1.1 hJ.2)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNPAt, tiB, tiNAt] at hJ ⊢
    obtain ⟨-, rfl, ⟨hsp, hfp, hs⟩, hdi⟩ := hJ
    rw [tiCall_run]
    refine .inl ⟨TI.call, rfl, rfl, rfl, ⟨rfl, ?_, ?_, ?_, ?_⟩, ?_⟩
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
    cases b
    case true => exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => absurd h (by decide)
    refine seg_fixW true ((call_nd_FWP (KC := True) (nC := tiNAt lab q xr .call) (e0 := 0) (lo' := -200)
      (hi' := 8) (M := StackM rS) (P := P)
      (Ne := fun g => takeNG lab (tiTake q g) false .e) (Ex := fun g => takeXG lab (tiTake q g) true)
      hR hFt0 (by show R.lo ≤ -48 - 0 + -200; omega) (by decide) (by show (-48 : Int) - 0 < R.hi; omega)
      (by show (-48 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-48 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide)
      (fun _ => TakeK.kstable fun m pm ⟨hD, _⟩ => ⟨hFt m pm hD, fun _ => stackM_takeMem⟩)
      (fun _ s s' hk _ k hk' _ => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (hRS k hk'))
      (fun m h hM => ⟨⟨h.1, fun _ => hM⟩, nofun⟩)
      (fun R' F' hR' hlo' hhi' hF' hK' hFF' hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, h48⟩, ⟨-, -, -, hra, -⟩⟩ := hg'
        have hr : g'.ra = (lab xr).toBitVec := by
          have e : lab xr = Int64.ofBitVec g'.ra := by
            rw [← hra]
            show lab _ = Int64.ofBitVec (σC.slot (-48 - 0 + 0))
            rw [show (-48 : Int) - 0 + 0 = -48 by decide, h48, int64_ofBitVec_toBitVec]
          rw [e]; rfl
        exact (stackTake_segWA hp hend hst hF' hR' hlo' hhi' (fun m h => hFF m (hFF' m h).1) (tiTake q g') hk
          ((htk g').mono fun m h => (hFF' m h).1)
          (FStable.callee hR (show R.lo ≤ -48 - 0 + -200 by omega) (by decide) (show (-48 - 0 : Int) < R.hi by omega)
            (show (-48 - 0 : Int) + 8 ≤ R.hi by omega) hP)
          (fun i => (hW TI.call g' hr i).shift fun m h => ⟨(hFF' m h).1, hcc m h⟩) hRS' hfit hout'
          (takeMem_of_kstable (hK' trivial) exe endPc)).mono_post
          fun s c ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM⟩, hJ⟩ => ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM⟩)
      (fun _ => rfl) ?_ ?_).mono_pre
        fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD.1, hD.2 rfl⟩, hJ.2⟩)
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
    refine SegW.mono_pre (P := At exe endPc R (fun m => takeF F rS b m ∧ (b = false → P m))
      (tiA b (tiX7At lab q xr))) ?_
      fun _ _ h => At.rbp h fun σ c ⟨_, _, ⟨hsp, hfp, _⟩, _⟩ => by
        simp only [Reg64s.get64]; rw [hsp, hfp]; bv_omega
    refine seg_ndW (by simp [ThreadInit.tiSp]) ThreadInit.tiSp_ok hFb hR (by omega) hhi
      (code_field hp hend (by simp only [hin']) (l := xr) (off := 0) (ofNat_zero' _))
      (blkW_tiSP (hWt TI.x7 nofun)) fun σ c hJ => ⟨c, .refl c, ?_⟩
    dsimp only [tiNGAt, tiA, tiX7At, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiSp_walk lab _ hJ ha
    exact .inl ⟨TI.st0, by rw [h1]; rfl, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st0 =>
    refine seg_fixW b ?_
    snodeWA 0 0 48 3 q.tcb TI.f1 (nodeW_tiSP (hWt TI.st0 nofun))
  case f1 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF1 ThreadInit.tiF1_ok xr 51 (blkW_tiSP (hWt TI.f1 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF1_walk lab _ hJ
    exact .inl ⟨TI.st1, by rw [h1]; exact ofNat_add' _ 51 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st1 =>
    refine seg_fixW b ?_
    snodeWA 1 8 59 4 (tiBase (_root_.Executable.labels exe).label q + 4096#64) TI.f2
      (nodeW_tiSP (hWt TI.st1 nofun))
  case f2 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiZ ThreadInit.tiZ_ok xr 63 (blkW_tiSP (hWt TI.f2 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st2, by rw [h1]; exact ofNat_add' _ 63 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st2 =>
    refine seg_fixW b ?_
    snodeWA 2 16 74 4 (0#64) TI.f3 (nodeW_tiSP (hWt TI.st2 nofun))
  case f3 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiZ ThreadInit.tiZ_ok xr 78 (blkW_tiSP (hWt TI.f3 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiZ_walk lab _ hJ
    exact .inl ⟨TI.st3, by rw [h1]; exact ofNat_add' _ 78 11, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st3 =>
    refine seg_fixW b ?_
    snodeWA 3 24 89 4 (0#64) TI.f4 (nodeW_tiSP (hWt TI.st3 nofun))
  case f4 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF4 ThreadInit.tiF4_ok xr 93 (blkW_tiSP (hWt TI.f4 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF4_walk lab _ hJ
    exact .inl ⟨TI.st4, by rw [h1]; exact ofNat_add' _ 93 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st4 =>
    refine seg_fixW b ?_
    snodeWA 4 32 101 4 (tiBase (_root_.Executable.labels exe).label q) TI.f5
      (nodeW_tiSP (hWt TI.st4 nofun))
  case f5 =>
    refine seg_fixW b ?_
    inodeWA ThreadInit.tiF5 ThreadInit.tiF5_ok xr 105 (blkW_tiSP (hWt TI.f5 nofun))
    dsimp only [tiNGAt, tiA, tiNAt] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := ThreadInit.tiF5_walk lab _ hJ
    exact .inl ⟨TI.st5, by rw [h1]; exact ofNat_add' _ 105 8, by rw [h2]; rfl, rfl, rfl, h3, h4, h5⟩
  case st5 =>
    refine seg_fixW b ?_
    snodeWA 5 40 113 4 (tiBase (_root_.Executable.labels exe).label q + 16384#64) TI.ret
      (nodeW_tiSP (hWt TI.st5 nofun))
  case ret =>
    refine seg_fixW b ?_
    inodeWX ThreadInit.tiRet ThreadInit.tiRet_ok xr 117 3 ThreadInit.retL (blkW_tiSP (hWt TI.ret nofun))
    dsimp only [tiNGAt, tiA, tiNAt, tiXG, tiX] at hJ ⊢
    obtain ⟨rfl, rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := ThreadInit.tiRet_walk lab _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, rfl, h3⟩

end TiWProofAtAC

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.TakeWP.shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TakeWP.shift

/-- info: 'Spike.Lib.X64.Rt.threadInit_segWAtAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.threadInit_segWAtAC
