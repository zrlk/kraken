/-
**`scc_rt_start`'s states inside `W2`, for any placed output**
(`startEW_w2`): the obligations `StartEW` (`Spike/Lib/Rt/A64StartE.lean`)
at `nilW W2`, not moved by the take's outside move, from `_start` to
`bl scc_rt_main`: each node's obligation inside `SFacts` (`startEW_sfacts`)
and inside `RtX` (`startEW_rtX`), the two giving `W2` (`rtX_w2`).

- `swEW_gen`: the switch and the block after it inside `SFacts`, for any
  program with the start's tail (`swUW_gen`'s first two obligations);
- `TcbW.imp` … `StartEW.imp`: an obligation inside `W` from one inside
  `W1` not moved by `K` and one inside `W2` (`BlkW.imp`, `NodeW.imp`);
- `startEW_sfacts`: `StartEW` inside `SFacts` at a placed output
  (`entryW_ofPlaceOK`, `startSp_gen`, `swEW_gen`);
- `startEW_w2`: the two combined;
- `rtWords_offArena`: the runtime's words off the output's arena `arOf`;
- `mainHead_of_placeOKAt`, `mainPosOff_of_placeOKAt`: `scc_rt_main`'s head
  (A11, either tail), so `hmain`;
- `startEW_w2A`: `startEW_w2` at `arOf` with both, and the words off the
  arena's counter by `hctr_of_placeOKAt`: no premise left.
-/
import Spike.Lib.LowerA64.RtStartXOf
import Spike.Lib.Rt.A64ArenaOfPlaceOK
import Spike.Lib.Rt.A64MainS
import Spike.Lib.Rt.A64RtMainU
import Spike.Lib.Rt.A64EntryOfPlaceOK
import Spike.Lib.Rt.A64SegsS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (TcbG TN TcbW TakeG TK TakeW TiG TI TiW Sp0W Sp2W StackM pinA stacksA)
open Spike.Lib.A64.Rt (StartEW SwEW RuntimeLayout)
open Spike.Lib.A64.AllocG (BlkW.imp NodeW.imp)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-! ## The switch inside `SFacts` -/

section Sw

open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.MainU
open Spike.Lib.A64.Flow.Ret0 (startTailIn startMain)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl}

/-- **The switch and the block after it are inside `SFacts`** (`SwEW`), for
any program with the start's tail (`hin`): `swUW_gen`'s first two
obligations, without `scc_rt_main`'s code. -/
theorem swEW_gen {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : startTailIn prog = true) {c0 : Ctl} (hC0 : CFacts Λ lbl c0) (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64} {L : Int}
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK) (hL8 : L % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    SwEW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) rS tcb top
      c0 L := by
  have h := hin
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨-, bSw⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_⟩
  · rw [hI.labOk]
    exact nodeW_flowReg_post hI (by simp [Spike.Lib.A64.Flow.RegOnly]) bSw rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hsw.sw.1
      hsw.sw.2 hsub
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact blkW_postO hI bMain rfl (startMain_okL (-L) 0) hok h16 (Int.le_refl _) (Int.le_refl _)
        (fun _ _ hJ => hJ.1 ▸ hC0) hsw.main
        (fun _ _ _ k hk r hr => (noRet_false startMain_noRet k hk r hr).elim) (fun _ _ _ => rfl)
        (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hsub hfit (fun _ h => h.2)
    · exact blkW_ofFalse fun _ h => hv h.1.1

end Sw

/-! ## Two obligations in one -/

section Imp

variable {W1 W2 W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F M : MachineData → Prop}

/-- `scc_rt_alloc_tcb`'s obligations inside `W` from two. -/
theorem TcbW.imp {q : TcbG} {i : TN} (h1 : TcbW W1 K exe endPc R F q i)
    (h2 : TcbW W2 (fun _ _ => False) exe endPc R F q i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TcbW W K exe endPc R F q i := by
  cases i <;> dsimp only [TcbW] at h1 h2 ⊢ <;> first | exact BlkW.imp h1 h2 hw | exact NodeW.imp h1 h2 hw

/-- `scc_rt_stack_take`'s obligations inside `W` from two. -/
theorem TakeW.imp {q : TakeG} {i : TK} (h1 : TakeW W1 K exe endPc R F M q i)
    (h2 : TakeW W2 (fun _ _ => False) exe endPc R F M q i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TakeW W K exe endPc R F M q i := by
  cases i <;> dsimp only [TakeW] at h1 h2 ⊢ <;>
    first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw
    | exact ⟨NodeW.imp h1.1 h2.1 hw, NodeW.imp h1.2 h2.2 hw⟩
    | exact fun s c hA => hw s c (h1 s c hA) (h2 s c hA)

/-- `scc_rt_thread_init`'s obligations inside `W` from two. -/
theorem TiW.imp {q : TiG} {i : TI} (h1 : TiW W1 K exe endPc R F M q i)
    (h2 : TiW W2 (fun _ _ => False) exe endPc R F M q i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TiW W K exe endPc R F M q i := by
  cases i <;> dsimp only [TiW] at h1 h2 ⊢ <;>
    first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw
    | exact fun g hg j => TakeW.imp (h1 g hg j) (h2 g hg j) hw

/-- `scc_rt_start`'s first nodes inside `W` from two. -/
theorem StartW.imp {J : AS → Ctl → Prop} (h1 : StartW W1 K exe endPc R F J)
    (h2 : StartW W2 (fun _ _ => False) exe endPc R F J) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    StartW W K exe endPc R F J :=
  ⟨BlkW.imp h1.w0 h2.w0 hw, NodeW.imp h1.w1 h2.w1 hw, NodeW.imp h1.w2 h2.w2 hw, BlkW.imp h1.w3 h2.w3 hw,
    NodeW.imp h1.w4 h2.w4 hw⟩

/-- `scc_rt_start` up to `.sp2` inside `W` from two. -/
theorem Sp0W.imp {n0 : BitVec 64} {c0 : Ctl} (h1 : Sp0W W1 K exe endPc R F n0 c0)
    (h2 : Sp0W W2 (fun _ _ => False) exe endPc R F n0 c0) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    Sp0W W K exe endPc R F n0 c0 :=
  ⟨StartW.imp h1.start h2.start hw, BlkW.imp h1.blk h2.blk hw,
    fun g hg i => TcbW.imp (h1.tcb g hg i) (h2.tcb g hg i) hw⟩

/-- `scc_rt_start` from `.sp2` to the switch inside `W` from two. -/
theorem Sp2W.imp {rS : Range} {n0 k0 : BitVec 64} {c0 : Ctl} (h1 : Sp2W W1 K exe endPc R F rS n0 k0 c0)
    (h2 : Sp2W W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    Sp2W W K exe endPc R F rS n0 k0 c0 :=
  ⟨BlkW.imp h1.b2 h2.b2 hw, fun g hg i => TiW.imp (h1.ti g hg i) (h2.ti g hg i) hw, BlkW.imp h1.b3 h2.b3 hw,
    NodeW.imp h1.msr h2.msr hw⟩

/-- The switch and the block after it inside `W` from two. -/
theorem SwEW.imp {rS : Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (h1 : SwEW W1 K exe endPc R F rS tcb top c0 L) (h2 : SwEW W2 (fun _ _ => False) exe endPc R F rS tcb top c0 L)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : SwEW W K exe endPc R F rS tcb top c0 L :=
  ⟨NodeW.imp h1.sw h2.sw hw, fun v => BlkW.imp (h1.blk v) (h2.blk v) hw⟩

/-- **The start's obligations up to `scc_rt_main`'s entry inside `W`** from
two. -/
theorem StartEW.imp {rS : Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int}
    (h1 : StartEW W1 K exe endPc R F rS n0 k0 c0 L) (h2 : StartEW W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0 L)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : StartEW W K exe endPc R F rS n0 k0 c0 L :=
  ⟨BlkW.imp h1.e h2.e hw, Sp0W.imp h1.s1 h2.s1 hw, Sp2W.imp h1.s2 h2.s2 hw, SwEW.imp h1.s3 h2.s3 hw⟩

end Imp

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Rt.PhRecOf in
/-- **`scc_rt_start`'s states are inside `SFacts`** (`StartEW`, from
`_start` to `bl scc_rt_main`) at the record of an output passing `placeOK`,
in any region holding its frame and its callees' below, with the source
control `c0` (`hC0`), the frame condition giving the runtime's words
unloaded (`hFr`), the first TCB (`hn0`) and the first stack `rS` (`hrS`) in
the pool (`hsub`) kept by the writes of the three regions (`hSM`, `hSMi`,
`hSMt`), not wrapping (`hfit`), and the new stack's top 16-aligned with its
region of 8-aligned depth `L` (`h16`, `hok`, `hL8`). -/
theorem startEW_sfacts {lbl : Lbl} {rS : Range} {c0 : Ctl} {R : Region} {F : MachineData → Prop}
    {n0 k0 : BitVec 64} {L : Int}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0)
      (StackM rS))
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (h16 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL8 : L % 8 = 0) :
    StartEW (fun s c => SFacts (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.PhRec.own (Ly)) rS
        (Spike.Lib.A64.PhRec.Tk (Ly)) lbl s c) (Spike.Lib.A64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS n0 k0
      c0 L := by
  have hrt : Scc.Cert.Rt.A64.rtPhOk (Ly).Λ.code.lo o.prog (Ly).Λ (Spike.Lib.A64.Rt.rtPhTab none) = true :=
    rtPh_of_placeOKAt h
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hsp := Spike.Lib.A64.Rt.startSp_gen h i hrt hC0 hR hal hlo hhi hFr hn0 hrS hsub hSM hSMi hSMt
    (Dt := fun _ => False)
  refine ⟨Spike.Lib.A64.Rt.entryW_ofPlaceOK h i hR hal (by omega) hhi hC0, hsp.1, hsp.2, ?_⟩
  exact swEW_gen hI (Spike.Lib.A64.Rt.rtCode0_of_placeOKAt h).tail hC0 (swPh_ofPlaceOK h i hrt)
    (by rw [hI.labOk]; exact h16) (by rw [hI.labOk]; exact hok) hL8 hsub hfit

open Spike.Lib.LowerNode (FrOk2 ZBad) in
/-- **`scc_rt_start`'s states are inside `W2`** (`StartEW` at `nilW W2`,
from `_start` to `bl scc_rt_main`, not moved by the take's outside move) at
the record of an output passing `placeOK`, at the source start's control
`A64Consumer.c0` (`hC0`, `hf0`, placed at no frame `hpl0`) of a program free
of `ZBad` (`hp`): `startEW_sfacts`'s premises, room for the first stack
(`hk`), the runtime's words off the arena's counter and heap (`hoff`) and
`scc_rt_main` positioned off the write abort (`hmain`). -/
theorem startEW_w2 {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl lbl0 : Lbl} {lsize : Lsize} {rS : Range} {R : Region} {F : MachineData → Prop}
    {k0 : BitVec 64} {L : Int} (hp : ProgNoS ZBad p) (hf0 : FrOk2 A64Consumer.c0 [])
    (hC0 : CFacts (Ly).Λ lbl0 A64Consumer.c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0)
      (StackM rS))
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (h16 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL8 : L % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hoff : ∀ a ∈ (Ly).rtWords, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hmain : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main"))
    (hpl0 : ∀ s, PlacedS (Ly).Λ lbl s A64Consumer.c0 []) :
    StartEW (Spike.Lib.A64.Rt.nilW (W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G (Spike.Lib.A64.PhRec.own (Ly))
        rS (Spike.Lib.A64.PhRec.Tk (Ly)) ar J Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) lbl lsize))
      (Spike.Lib.A64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 A64Consumer.c0 L :=
  StartEW.imp (startEW_sfacts h i hC0 hR hal hlo hhi hFr rfl hrS hsub hSM hSMi hSMt hfit h16 hok hL8)
    (startEW_rtX h i (rS := rS) hR hal hlo hhi hFr rfl hk hoff hmain h16 hok hpl0)
    fun _ _ hS hX => by
      obtain rfl := hX.2.2.2
      exact rtX_w2 hp hf0 hS hX

/-- **The runtime's words are off the arena** `arOf` of the output's
layout: their first bytes lie in `.data` or `pinned` (`words_mapped`), both
disjoint from the heap (A1), which holds the arena (`arOf_sub`). -/
theorem rtWords_offArena : ∀ a ∈ (Ly).rtWords,
    ¬ ((Spike.Lib.A64.Rt.arOf (Ly).Λ).heap ≤ a.toNat ∧
      a.toNat < (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells) := by
  intro a ha
  have hs := Spike.Lib.A64.Rt.arOf_sub h
  have hwf := wf_of_placeOKAt h
  have hD := hwf.disjoint.2.2.2.1
  have hP := hwf.disjoint.2.2.2.2.2.2.2.2.1
  have hb := ((Ly).words_mapped a ha).2.2 0 (by omega)
  change Λ.data.contains (a.toNat + 0) ∨ Λ.pinned.contains (a.toNat + 0) at hb
  change ¬ ((Spike.Lib.A64.Rt.arOf Λ).heap ≤ a.toNat ∧
    a.toNat < (Spike.Lib.A64.Rt.arOf Λ).heap + 16 * (Spike.Lib.A64.Rt.arOf Λ).cells)
  simp only [Range.Sub, Range.Disjoint, Range.contains] at hs hD hP hb
  omega

include h in
/-- **`scc_rt_main`'s head at a placed output** (A11, either tail): its
label right before its stack check, whose first block is `chkHead` at some
frame. -/
theorem mainHead_of_placeOKAt : ∃ Z, Scc.Cert.Rt.A64.labelGap o.prog "scc_rt_main"
      ".L1_scc_rt_main.stack_check" 0 = true ∧
    Scc.Cert.Rt.A64.blockAt o.prog ".L1_scc_rt_main.stack_check" 0 (chkHead Z) = true := by
  cases hs : o.place.tail with
  | bare =>
    have hm := (Spike.Lib.A64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)).main
    simp only [Spike.Lib.A64.Rt.mainUIn, prologueIn, Bool.and_eq_true] at hm
    exact ⟨_, hm.1.1.1.1.1.1.1.1, hm.1.1.1.1.1.1.1.2⟩
  | setup =>
    obtain ⟨sw, -, hw⟩ := List.any_eq_true.mp (setupOk_of_placeOKAt h hs)
    have hm := Spike.Lib.A64.Rt.mainSIn_of_okS (Bool.and_eq_true _ _ ▸ hw).1
    simp only [Spike.Lib.A64.Rt.mainSIn, prologueIn, Bool.and_eq_true] at hm
    exact ⟨_, hm.1.1.1.1.1.1.1.1.1.1, hm.1.1.1.1.1.1.1.1.1.2⟩

/-- **`hmain`: `scc_rt_main` is a position off the write abort** at a
placed output: the first instruction of its stack check, right after its
label (`mainHead_of_placeOKAt`). -/
theorem mainPosOff_of_placeOKAt : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main") := by
  obtain ⟨Z, hg, hb⟩ := mainHead_of_placeOKAt h
  refine posOff_of_labelGap (Ly).lays hg ?_
  have := posOff_of_blockAt (lab := (Ly).lab) hb (by decide) (i := 0) (by simp [chkHead])
  rwa [ofNat4_zero] at this

open Spike.Lib.LowerNode (FrOk2 ZBad) in
/-- **`scc_rt_start`'s states are inside `W2` at the output's arena**
(`startEW_w2` at `arOf`): the runtime's words off the arena by
`rtWords_offArena` and its counter by `hctr_of_placeOKAt`, and `scc_rt_main`
off the write abort by `mainPosOff_of_placeOKAt`. -/
theorem startEW_w2A {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {lbl lbl0 : Lbl} {lsize : Lsize} {rS : Range} {R : Region} {F : MachineData → Prop}
    {k0 : BitVec 64} {L : Int} (hp : ProgNoS ZBad p) (hf0 : FrOk2 A64Consumer.c0 [])
    (hC0 : CFacts (Ly).Λ lbl0 A64Consumer.c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).Λ.stackPool)
    (hSM : FStable R (StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee Ret0.ThreadInit.oI.sp (-208) 0)
      (StackM rS))
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (h16 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL8 : L % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ lbl s A64Consumer.c0 []) :
    StartEW (Spike.Lib.A64.Rt.nilW (W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p rd G (Spike.Lib.A64.PhRec.own (Ly))
        rS (Spike.Lib.A64.PhRec.Tk (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ) J Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab)
        lbl lsize))
      (Spike.Lib.A64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 A64Consumer.c0 L :=
  startEW_w2 h i (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) hp hf0 hC0 hR hal hlo hhi hFr hrS hsub hSM hSMi hSMt
    hfit h16 hok hL8 hk
    (fun a ha => ⟨Spike.Lib.A64.Rt.RuntimeLayout.hctr_of_placeOKAt h i a ha, rtWords_offArena h i a ha⟩)
      (mainPosOff_of_placeOKAt h i) hpl0

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.swEW_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swEW_gen

/-- info: 'Spike.Lib.LowerA64.StartEW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StartEW.imp

/-- info: 'Spike.Lib.LowerA64.startEW_sfacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_sfacts

/-- info: 'Spike.Lib.LowerA64.startEW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_w2

/-- info: 'Spike.Lib.LowerA64.rtWords_offArena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtWords_offArena

/-- info: 'Spike.Lib.LowerA64.mainPosOff_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainPosOff_of_placeOKAt

/-- info: 'Spike.Lib.LowerA64.startEW_w2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_w2A

end Spike.Lib.LowerA64
