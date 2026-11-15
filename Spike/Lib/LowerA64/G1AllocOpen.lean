/-
**The allocator's `W2` instance at the landings' contexts, for any
`Accepted2` program** (AArch64): the per-allocation bundle `AllocPtV`
(`Spike/Lib/LowerA64/G1AllocPt.lean`) at every allocation of the setup
block, at every choice of the bounds and landing context `CxOkH`, closed
for any `Accepted2` program with a setup block whose object layout puts a
one-word element's header below the allocator's trace-count field
(`hobj`), and so `OpenAHA` there.

The fields of `AllocPtV` at an allocation:

- `hu`, `hacc`, `hnr`: `allocPt_of_accepted2` (at the record's arena,
  `AllocPtWk.ofAr`; the frames `[fr]` of `CxOkH`);
- `hms`: `callMsOK_arOf` at the Linux entry (the record's executable), the
  value invariant free at the counter and the heap (`gOf_ctr_arOf`,
  `gOf_heap_arOf`), the header without trace words (`mOf_header_elem2`:
  a one-word element's counts are `(1, 0)`, `countsO_elem2`, and its header
  lies below bit 22 when `nShift < 22`);
- `hxa`, `hxaF`: `landStk_hxa` at the context `CxOkH` with no records, as
  for `hello1`;
- `hstub`: `hello1_hstubA` (`Spike/Test/A64Hello1AllocStubH.lean`, generic
  in the program).

- `OpenAPtV`: `allocW2At_ofV`'s `hpt` at `AllocWH`'s instance (`OpenAPtA`
  with `AllocPtV`);
- `cxLB_hAW_noneV`: `OpenAHA` from `OpenAPtV` (`cxLB_hAW_noneA` by
  `allocW2At_ofV`);
- `openAPtV_of_accepted2`: `OpenAPtV` at any `Accepted2` program with a
  setup block, at the landings `ElH` and the write tail `fun _ => True`;
- `openAHA_of_accepted2`: `OpenAHA` there.
-/
import Spike.Test.A64Hello1HAWNone
import Spike.Test.A64Hello1AllocStubH
import Spike.Lib.LowerA64.LandStk2
import Spike.Lib.LowerA64.LandHu
import Spike.Lib.LowerA64.G1AllocPt

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)

/-! ## A one-word element's header -/

/-- **A one-word element's counts are `(1, 0)`**: `countsO` is the element's
register counts (`regOf`) when defined, and an `elem2` type is one scalar
slot. -/
theorem countsO_elem2 {o : Scc.ObjLayout} {τ : Ty} {en em : Nat}
    (h : Spike.Lib.LowerShape.countsO o τ = some (en, em)) (he : Scc.Lower.elem2 τ = true) : en = 1 ∧ em = 0 := by
  have hr : Scc.Obj.regOf τ = some (1, 0) := by
    cases τ <;> simp [Scc.Lower.elem2] at he <;> rfl
  simp only [Spike.Lib.LowerShape.countsO, hr, Option.bind_eq_bind, Option.bind_some] at h
  cases hc : Scc.Obj.counts o τ with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.bind_some] at h
    split at h
    · rename_i hce
      cases h
      simp_all
    · cases h

/-- **A one-word element's array header has no trace words for the
allocator** (`mOf`, the header's bits from 22): with the scalar count's
field starting below bit 22 (`hobj`), the header `1 + 2 ^ nShift` of
counts `(1, 0)` lies below `2 ^ 22`. -/
theorem mOf_header_elem2 {o : Scc.ObjLayout} (hobj : Scc.Obj.nShift o < 22) {τ : Ty} {en em hh : Nat}
    (he : Scc.Lower.elem2 τ = true) (hco : Spike.Lib.LowerShape.countsO o τ = some (en, em))
    (hhd : Scc.Obj.header0 o .array en em = some hh) : (Spike.Lib.A64.Alloc.mOf (BitVec.ofNat 64 hh)).toNat = 0 := by
  obtain ⟨rfl, rfl⟩ := countsO_elem2 hco he
  simp only [Scc.Obj.header0] at hhd
  split at hhd
  · cases hhd
    have h21 : 2 ^ Scc.Obj.nShift o ≤ 2 ^ 21 := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : Scc.Obj.HeaderKind.code .array + 1 * 2 ^ Scc.Obj.nShift o + 0 * 2 ^ Scc.Obj.mShift o < 2 ^ 22 := by
      simp only [Scc.Obj.HeaderKind.code]; omega
    have h0 : BitVec.ofNat 64 (Scc.Obj.HeaderKind.code .array + 1 * 2 ^ Scc.Obj.nShift o +
        0 * 2 ^ Scc.Obj.mShift o) >>> 22 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt h1]
      rfl
    simp only [Spike.Lib.A64.Alloc.mOf]
    rw [h0]
    rfl
  · cases hhd

/-- **The allocation's call context at another frame invariant**: the rows'
memory sides at `I` and `I'` differ only in what `AllocCtx` does not read
(`msOfAX` at either abort). -/
theorem allocCtx_msOfAX {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Spike.Lib.Arena} {I I' : InvS} {ab : Option (State → Prop)}
    {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {L : Label → Int64} {R : Region} {fr : Int}
    {Jc : AS → Ctl → Prop} {q : Spike.Lib.A64.Alloc.Call} {m : MachineData}
    (h : Spike.Lib.A64.Flow.NewBuf.AllocCtx (msOfAX Λ μ p rd G own ar I ab lbl lsize fs) L R fr Jc q m) :
    Spike.Lib.A64.Flow.NewBuf.AllocCtx (msOfAX Λ μ p rd G own ar I' ab lbl lsize fs) L R fr Jc q m := by
  cases ab <;> exact h

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)
set_option hygiene false in
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
set_option hygiene false in
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)
set_option hygiene false in
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
set_option hygiene false in
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs
set_option hygiene false in
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)
set_option hygiene false in
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m
set_option hygiene false in
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs
set_option hygiene false in
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)
set_option hygiene false in
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64
set_option hygiene false in
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64
set_option hygiene false in
local notation "TP0" => UInt64.ofBitVec (X0)
set_option hygiene false in
local notation "FS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m
set_option hygiene false in
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
    (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs
set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option linter.unusedVariables false in
/-- **`allocW2At_ofV`'s per-allocation premise `hpt` at `AllocWH`'s instance**,
at every choice of the bounds, family `J` containing the starts and context
`CxOkH` with the setup frame's bottom key (`hd` is read by `FC`, which the
unused-variables linter does not see through). -/
def OpenAPtV (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ (v : BitVec 64) (j : Nat) (d : Decl) (hd : (compiled2 p)[j]? = some d),
      d.name = "rodata" →
    ∀ (R : Region) (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64)
      (G0 : Ctl → Prop) (Ab' : FragS isaLSE2), CxOkH h hp j R F fs fp ra tp G0 Ab' →
      (SB J v D1 fS) ⟨j, R, F, fp, ra, tp, G0⟩ fs →
    ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : At) (τ : Ty) (e : Expr)
      (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
      (tk : Ty) (kv : UInt64) (en em hh : Nat), G0 c0 → TailAt2 p j (.let_ x (.newBuf cn τ) e) →
      Spike.Lib.LowerNode.Fresh env n → Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
      Spike.Lib.LowerShape.countsO (FC).lcx.obj τ = some (en, em) →
      Scc.Obj.header0 (FC).lcx.obj .array en em = some hh →
      PtC2 (FC).lcx (FC).cx
        (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
        (BlC2L OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (FC).cx
          (Int64.ofBitVec ra))
        (_root_.Executable.labels (Ly).exe).label (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) kk pc env n lits
        cs bufs (.let_ x (.newBuf cn τ) e) →
      AllocPtV (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
        (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
        (fun _ => none) (fun _ => 0) (S0A h E (WNF)) El J (ab2 p (Ly).lab) Dt (LY0).lab
        ((Ly).lab StackTake.siteL) (fun _ => none) (fun _ => 0) fs (Ly).exe (Ly).endPc R F (FC).cx fp ra tp
        c0 pc x cn τ e env lits cs bufs hh kv
        (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)

/-- **`OpenAHA` from the per-allocation premises `OpenAPtV`**
(`allocW2At_ofV` at every `CxOkH` context): the record's facts from the
placement check, the frame's from `fnCode2OfPMe`, the region's from
`CxOkH`'s `PRE` and bounds (as `hAW_CxOkH`), the frame placed at no label,
the arena's words from `ArCallMs` at `CxOkH`'s `WordsNone`, the ghosts along
the setup frame's run, the elements by `hTn`. -/
theorem cxLB_hAW_noneV (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    (H : OpenAPtV h hp E El Dt) : OpenAHA h hp E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn R F fs fp ra tp G0 Ab' hc hSB
  have HP := H L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn R F fs fp ra tp G0 Ab' hc hSB
  obtain ⟨d', hd', L', D1', fS', nS', v', g, fr, J', -, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, hwn, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).cx.frame = fS' := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo0 : -D1' ≤ -((FC).cx.frame : Int) := by rw [hframe]; omega
  have hhi : (0 : Int) ≤ 0 := Int.le_refl _
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hFO : ∀ m, F m → StackOff (rS0 (Ly))
      ((swR v' (-L') 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1') 0) m := by
    intro m hm
    obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L') 0).base.toNat % 8 = 0 := by
      show (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L') % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L' ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hc := Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h
  haveI : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨-, -, -, -, hH, hCt, hU, hO, hCl, -⟩ := msOfAX_fields (Λ := (Ly).Λ) (μ := Spike.Lib.A64.PhRec.μ (Ly))
    (p := p) (rd := Spike.Lib.LowerNode.IsNum) (G := G2 h p) (own := fun s _ => Spike.Lib.A64.PhRec.own (Ly) s)
    (ar := Ar) (I := IN (Ar) (fun _ => none) (fun _ => 0) J) (lbl := fun _ => none) (lsize := fun _ => 0)
    (fs := [fr]) (ab2 p (Ly).lab)
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
  exact allocW2At_ofV (ownOf := Spike.Lib.A64.PhRec.ownOf (Ly))
    (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))) (allocIn_of_placeOKAt h)
    (Spike.Lib.A64.Rt.allocPhOk_ofPlaceOK h (Scc.Lower.imms2Of p))
    (Spike.Lib.A64.Rt.allocAbOk_ofPlaceOK h (Scc.Lower.imms2Of p)) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) (fun _ => rfl) (FC).hf (FC).h1 (FC).h16 hR0 hal
    (by show (-D1') % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
    (by show -D1' ≤ -((FC).cx.frame : Int) + -160 - 48; rw [hframe]; omega) hhi hF'
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO hpN hJ
    Reach.base (fun s _ => framesPlaced_setup h hp hty hct s)
    (fun _ _ hr => regionOff_of_rsOf (FC).hf hlo0 hhi hr)
    (fun q hq a ha => hmem_arOf h hc hwn hH hCl hCt hU hO q hq a (by rw [hCt, hU, hCl]; exact ha))
    (hno_arOf h (imms2Me Λ p) hH hO) (hlt_arOf h hc) (h64_arOf h hc)
    (fun _ _ _ _ _ hl => nomatch hl) (hTn j d hd)
    (fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2A hty _))) HP

/-- **`OpenAPtV` at any `Accepted2` program with a setup block** (`hty`)
whose object layout starts the header's scalar count below bit 22
(`hobj`): `AllocPtV` at every allocation at every choice of the bounds,
family containing the starts and context `CxOkH` (see the module
docstring). -/
theorem openAPtV_of_accepted2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) :
    OpenAPtV h hp E (ElH h hp) (fun _ => True) := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v j d hd hn R F fs fp ra tp G0 Ab' hC hSB
    c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT hfr hat hco hhd hpt
  have hc := Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h
  -- the context with no records: its key the setup frame's bottom key
  have hcx : CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0)
      (fnCode2OfPMe hp h Λ) (CxOkH h hp)
      (BotH h) j R F fs fp ra tp G0 Ab' :=
    ⟨hC, [], ⟨J, L, D1, fS, v, D2, lS, lM, nS, fM, nM, hB, hSB⟩, d, hd, hn⟩
  -- the setup call's return address has the phase anchor's phase
  have hra : Spike.Lib.A64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.A64.PhRec.ph (LY0)
        (Int64.ofBitVec ((LY0).lab Spike.Lib.A64.Rt.bareMC.e0 + 4).toBitVec).toBitVec.toNat := by
    obtain ⟨-, -, -, -, -, -, -, g, fr, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, hgra, -⟩, -, -, -, -, -,
      hra, -⟩ := id hC
    rw [hra, hgra]
    exact raOk_setup _ _
  -- the allocation a resumption point of the block's code
  have hpt' : BodyPtW (fnCode2OfPMe hp h Λ j d hd) ra pc
      (.let_ x (.newBuf cn τ) e) env n lits cs bufs := by
    obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := hpt
    unfold BodyPtW
    rw [(fnCode2OfPMe_spec _ h _ j d hd).2.1]
    exact ⟨l, k, r, kk, h1, hfr, h2, h3, h4, h5, h6, h7⟩
  have he2 := (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1
  have hfs : fs ≠ [] := by
    obtain ⟨-, -, -, -, -, -, -, -, fr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfs, -⟩ := id hC
    rw [hfs]; exact List.cons_ne_nil _ _
  have H := allocPt_of_accepted2 Λ (Ly).Λ p hp j d hd _ _ _ _ _ _ kk pc env n lits cs bufs x cn τ e tk kv en em fs
    hat hco hpt hfs
  refine { toAllocPtWk := AllocPtWk.ofAr H, hms := ?hms, hxa := ?hxa, hxaF := ?hxaF, hstub := ?hstub }
  case hms =>
    intro q _ hτ hh'
    have hm : (Spike.Lib.A64.Alloc.mOf q.h).toNat = 0 := by
      rw [hh']
      exact mOf_header_elem2 hobj he2 (by rw [(fnCode2OfPMe_spec _ h _ j d hd).1] at hco; exact hco)
        (by rw [(fnCode2OfPMe_spec _ h _ j d hd).1] at hhd; exact hhd)
    have hq : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us := by rw [hτ]; exact H.hacc
    exact callMsOK_arOf h hc Entry.linux _ (gOf_ctr_arOf h _ _) (gOf_heap_arOf h _ _) hq hm
  case hxa =>
    intro la hla
    exact landStk_hxa (Spike.Lib.A64.Rt.arOf_ok h hc) (startsN_of_startsS hJ) Spike.Lib.AllocReach.Reach.base hd
      hcx hra hc0 hpt' ⟨tk, en, em, hat, hco, hhd, rfl⟩ hla (arOf_units_fit _)
  case hxaF =>
    intro la hla q hq J' hJ' l b w s c hl hAt htp
    -- the call's premises at the family `J'` (the memory sides differ only in `xa`)
    have hq' : q.OK (Spike.Lib.A64ConsumerA.msOfAX (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p
        Spike.Lib.LowerNode.IsNum (Spike.Lib.A64.PhRec.GOf (Ly) (Spike.Lib.A64.PhRec.m0Of (Ly).Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs))
        (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (lay2 Λ p)) (fun _ => none) (fun _ => 0) J')
        (ab2 p (Ly).lab) (fun _ => none) (fun _ => 0) fs) (_root_.Executable.labels (Ly).exe).label := by
      cases hab : ab2 p (Ly).lab <;> rw [hab] at hq <;>
        exact ⟨hq.term, hq.ev, hq.num, hq.hold, hq.n_lt, hq.ctr, hq.heap, hq.room, hq.cells, hq.units, hq.off,
          hq.accs, hq.rt, hq.mp, hq.grow, hq.hdr⟩
    exact landStk_hxa (J := J') (Spike.Lib.A64.Rt.arOf_ok h hc) hJ' Spike.Lib.AllocReach.Reach.base hd hcx hra
      hc0 hpt' ⟨tk, en, em, hat, hco, hhd, rfl⟩ hla (arOf_units_fit _) ⟨q, hq'⟩ _ (fun m hm => hm.1)
      (fun m hm => allocCtx_msOfAX hm.2.2) l b w s c hl hAt htp
  case hstub =>
    exact hello1_hstubA h hp hty hd hC he2 hpt

/-- **`OpenAHA` at any `Accepted2` program with a setup block**
(`cxLB_hAW_noneV` at `openAPtV_of_accepted2`, the elements by
`newBufK_of_accepted2`). -/
theorem openAHA_of_accepted2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) :
    OpenAHA h hp E (ElH h hp) (fun _ => True) :=
  cxLB_hAW_noneV h hp hty (fun _ _ hd _ _ _ _ hT => (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1)
    (openAPtV_of_accepted2 h hp hty hobj E)

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.countsO_elem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.countsO_elem2

/-- info: 'Spike.Lib.LowerA64.mOf_header_elem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mOf_header_elem2

/-- info: 'Spike.Lib.LowerA64.allocCtx_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.allocCtx_msOfAX

/-- info: 'Spike.Lib.LowerA64.cxLB_hAW_noneV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxLB_hAW_noneV

/-- info: 'Spike.Lib.LowerA64.openAPtV_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.openAPtV_of_accepted2

/-- info: 'Spike.Lib.LowerA64.openAHA_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.openAHA_of_accepted2
