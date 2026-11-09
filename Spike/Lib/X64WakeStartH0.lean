/-
**`wake_start_wc_place`'s box premises at wake's arena** (x86-64): at the
arena `X64WakeOD.arW hpw i` (both the start's and the memory side's), the
clone phase `X64WakeOD.ClW`, and a start control `c0` about to box a zero
(`C0Box`: `let o = new z` with `z ↦ 0 : int`, wake's `main` after
`let z = zero int`), the box's call (`hq0`), the arena's facts (`hH`, `hHi`,
`hroom`, `hctr`, `hoff`), the box's cells (`hoB`, `hmp`), its word
(`hbox`), the clone phase (`hcl`) and `har` all hold.

- `C0Box`: the start control's box shape; its non-vacuity at `main`;
- `mp_heapW`, `mp_dataW`: a heap / `.data` word is mapped and shared at the
  memory side;
- `mp_cellW`: a box's fitting cell is mapped and shared (any `AGB`);
  these three at any owned words `own` (the memory side's other fields
  wake's);
- `rt_L0T`: no placed label of `L0T` at no static label covers any word of
  the heap or `.data` beyond its box (stated as `hrt0`'s shape for
  `L0T`/`ls0T`);
- `wake_start_wc_h0`: `wake_start_wc_place` at `arW`, `ClW`, the box
  premises discharged.

x86-64 twin of `Spike/Lib/A64WakeStartH0.lean` (namespace
`Spike.Lib.X64.WakePh.StartH0`, same names). **Where this differs from
AArch64**: the layout is `RuntimeLayout.ofPlaceWX` at `PlaceWX` (A64
`ofPlaceW` at `PlaceW`; the arena lemmas take `PlaceWX` directly, A64
through `PlaceW.link`); `wc_main`'s region is `wR (MainGlue.RS wcLsw v)
wcD` at `wcD = 328`, `wcLsw = 384` (A64 `wR (swR v (-384) 0) 336`), the box's
landing on its `fp (-8)`, the thread pointer `tpOf (tcbS Ly)`, `NoSetFsW`
(A64 `NoMsrW`), `hti` `MainGlue`'s (`Rt.TiWAtP` below `F`, A64 `Ret0.TiW`),
as `X64WakeStartPlace.wake_start_wc_place` states them. The shared-memory
`WSep` premise (`hs`) stays a premise: its x86-64 producer (the
`StartPlaceLy` twin of `wsep_W`) is not on this branch (A64 discharges it
by `StartPlaceLy.wsep_W`). The arena's units and offset are proved here
(A64 `LowerA64.arOf_units_pos`/`arOf_off_eq`): the x86-64 module holding
them imports a definition clash with `X64KeepTPW`.
-/
import Spike.Lib.X64WakeStartPlace
import Spike.Lib.X64WakeOD
import Spike.Lib.X64WakeLoadT
import Spike.Lib.LowerX64.HeapWOf
import Spike.Lib.X64WakePreA

namespace Spike.Lib.X64.WakePh.StartH0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W AGB BoxW bX wX)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS SegW PlaceWX)

/-- **The start control boxes a zero**: `let o = new z in e`, `z` an `int`
word of value `0`, no hold (wake's `main` after `let z = zero int`). -/
structure C0Box (c0 : Ctl) : Prop where
  term : ∃ e, c0.term = .let_ "o" (.new (.var "z") (some .int)) e
  ev : ∃ w : TermRun.Word, TermRun.evalAt c0.env (.var "z") = some (.int, [w]) ∧ w.val = .num 0
  hold : c0.hold = none

/-- `C0Box` holds at `main`'s control after `let z = zero int`. -/
example : C0Box ⟨.let_ "o" (.new (.var "z") (some .int)) (.let_ "c" (.publish (.var "o"))
    (.let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.X64WakeSrcDefs.spawnTerm)),
    [("z", .int, [TermRun.cst (.num 0)])], none⟩ :=
  ⟨⟨_, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd (Spike.Lib.X64WakeOG.gW hpw i cT)
  (fun s _ => Spike.Lib.X64.WakePh.ownG (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (AR) I L0 ls0 []

set_option hygiene false in
/-- The memory side at any owned words `own` (the box lemmas do not read them). -/
local notation "MSo" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd (Spike.Lib.X64WakeOG.gW hpw i cT) own (AR) I L0 ls0 []

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "WSL" => WS (Ly) a (AR) p Dt (Spike.Lib.X64.WakeOD.ClW hpw i) Ctx lbl lsize frM
  (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

section Mem

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc} {I : Spike.Lib.X64ConsumerS.InvS}
  {L0 : Lbl} {ls0 : Lsize} {own : Spike.Lib.X64ConsumerS.OwnS}

/-- **A heap word is mapped and shared** at the memory side. -/
theorem mp_heapW {a : BitVec 64} (h : ∀ k < 8, (Ly).Λ.heap.contains (a.toNat + k)) : (MSo).mp ⟨a, 8⟩ true :=
  ⟨Spike.Lib.LowerX64.mapped_K0_of_heap h, fun _ k hk => .inr (.inl (h k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))⟩

/-- **A `.data` word is mapped and shared** at the memory side. -/
theorem mp_dataW {a : BitVec 64} (h : ∀ k < 8, (Ly).Λ.data.contains (a.toNat + k)) : (MSo).mp ⟨a, 8⟩ true :=
  ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem fun k hk => .inl (h k hk),
    fun _ k hk => .inl (h k (by simpa [Scc.Sem.Kernel.locBytes] using hk))⟩

/-- The memory side's units of a type with accesses are positive, its offset one header word. -/
private theorem units_off {τ : Ty} (hacc : ∃ us, TermRun.accs (TermRun.close [] τ) = some us) :
    1 ≤ (MSo).units 1 τ ∧ (MSo).off 1 τ = 8 :=
  by
    obtain ⟨us, hus⟩ := hacc
    refine ⟨?_, ?_⟩
    · show 1 ≤ (Spike.Lib.X64.Rt.arOf (Ly).Λ).units 1 τ
      simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus]
      split <;> omega
    · show (Spike.Lib.X64.Rt.arOf (Ly).Λ).off 1 τ = 8
      simp only [Spike.Lib.X64.Rt.arOf, Arena.ofWords, hus, Nat.mul_zero]

/-- **A box's fitting cell is mapped and shared**: its word `heap + 16 o + 8`
lies in the heap (`heapSize_of_placeWX`, `heap_below_of_placeW`). -/
theorem mp_cellW (q : AGB MSo (Ly).lab) (o' : Nat) (_ : (MSo).lo o') (ho : o' + (MSo).units 1 q.1.τ ≤ (MSo).cells) :
    (MSo).mp ⟨BitVec.ofNat 64 ((MSo).heap + 16 * o' + (MSo).off 1 q.1.τ), 8⟩ true := by
  obtain ⟨hu, hf⟩ := units_off hpw i (μ := μ) (rd := rd) (cT := cT) (I := I) (L0 := L0) (ls0 := ls0) (own := own) q.2.toS.accs
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 :=
    Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW (Spike.Lib.PlaceWX.link i hpw)
  have hc : (MSo).cells = 4194304 := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MSo).heap = (Ly).Λ.heap.lo := rfl
  rw [hf]
  refine mp_heapW hpw i (own := own) fun k hk => ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Scc.Sem.Range.contains; omega

end Mem

/-- **`L0T` covers no word but its box's**: a placed label of `L0T` at no
static label is `tcb0`'s, of no cells at `ls0T`, so its range is empty. -/
theorem rt_L0T {Λ : Scc.Sem.Layout} (hstat : Λ.static = fun _ => none) (ls : Lsize) (a : Nat) :
    ¬ ∃ l b, Spike.Lib.X64WakeLoadT.L0T Λ l = some b ∧
      (Scc.Sem.lrange (Spike.Lib.X64WakeLoadT.ls0T ls) l b).contains a := by
  rintro ⟨l, b, hl, hc⟩
  obtain ⟨rfl, -⟩ := Spike.Lib.X64WakeLoadT.l0T_some hstat hl
  simp [Scc.Sem.lrange, Scc.Sem.Range.contains, Spike.Lib.X64WakeLoadT.ls0T, Spike.Lib.X64ConsumerA.updN] at hc
  omega

/-- **From `_start` to `wc_main`'s heap abort at wake's arena**:
`wake_start_wc_place` at `ar = ar' = arW hpw i` and `Cl = ClW hpw i`, the
start control boxing a zero (`hbx`), the counter zero-initialised (`hc`),
the second limit word pinned (`hpin2`), no placed label covering a word
(`hrt0`), the extra frame `P` stable in `entryR E` (`hP`) carried to the
thread init's take site; the box's premises discharged. `hs` (`WSep`) is
left to the caller. -/
theorem wake_start_wc_h0 {a : BitVec 64} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {p : Prog} {Dt : State → Prop} {Ctx : FragS isa} {lbl lbl' : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc}
    {I : Spike.Lib.X64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize} {pS : Prog} {lblS : Lbl}
    (hp : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hs : Spike.Lib.X64.WakePh.WSep (Ly) a) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.X64Consumer.CFacts (Ly).Λ lbl' c0)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) L0 ls0)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64WakeGOf2.lim2A (Ly))
    (hcT : cT ≠ ⟨(Ly).pinA + 16#64, 8⟩)
    (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hrt0 : ∀ a, ¬ ∃ l b, L0 l = some b ∧ (Scc.Sem.lrange ls0 l b).contains a) (hbx : C0Box c0)
    {P : MachineData → Prop} (hP : Spike.Lib.X64.FStable (entryR E) P)
    (hti : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable ((entryR E).callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K (Ly) RS0) F' → (∀ m, F' m → FWN m) →
      ∀ g, g.ra = ((Ly).lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ j,
      Spike.Lib.X64.Rt.TiWAtP (WSL) (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc
        (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM RS0)
        ⟨g, tcbS (Ly), 0#64, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L P j)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.X64.NoSetFsW (Spike.Lib.X64.WakeTP.tpG (tpOf (tcbS (Ly))) (WSL))
        (Spike.Lib.X64.PhRec.K (Ly) RS0))
      (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
      (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
      (tpXa MS (tpOf (tcbS (Ly)))) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC)
      (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.X64.NoSetFsW (Spike.Lib.X64.WakeTP.tpG (tpOf (tcbS (Ly))) (WSL))
        (Spike.Lib.X64.PhRec.K (Ly) RS0))
      (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
      (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
      (tpXa MS (tpOf (tcbS (Ly)))) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC))
    (hxa : ∀ v m0 σC l A s c, lblS l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
        (bX MS (Ly).lab (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) l A) s c →
      TP (tpOf (tcbS (Ly))) s → (MS).xa l A 1 s c) :
    SegW (WSL) (Spike.Lib.X64.PhRec.K (Ly) RS0) pS lblS MS
      (At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ P m) (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0))
      (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
          (wX MS (Ly).lab (wR (RS wcLsw v) wcD) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) .abort) s c ∧
        TP (tpOf (tcbS (Ly))) s) := by
  have hL := Spike.Lib.PlaceWX.link i hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hL
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = 4194304 := rfl
  have hct : (MS).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have hacc1 : ∃ us, TermRun.accs (TermRun.close [] .int) = some us := ⟨_, rfl⟩
  obtain ⟨hu1, hf1⟩ := units_off hpw i (μ := μ) (rd := rd) (cT := cT) (I := I) (L0 := L0) (ls0 := ls0)
    (own := fun s _ => Spike.Lib.X64.WakePh.ownG (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hacc1
  have hu2 : (MS).units 1 .int = 2 := rfl
  have hctrB : ∀ k < 8, (Ly).Λ.data.contains ((BitVec.ofNat 64 (MS).ctr).toNat + k) := fun k hk => by
    rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold Scc.Sem.Range.contains; omega
  have hG : ∀ a : BitVec 64, a.toNat < 2 ^ 32 → ((Ly).Λ.heap.contains a.toNat ∨ (Ly).Λ.data.contains a.toNat) →
      ∀ v, (MS).G ⟨a, 8⟩ v := fun a ha hm v => by
    have := Spike.Lib.X64WakeOG.hGpl_ofPlaceW2 hpw i hpin2 a.toNat v hm
    refine .inr ?_
    simpa [Scc.Sem.wordLoc] using this
  have hoff : ∀ q : Call, q.OKB MS (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ := fun q hq => by
    obtain ⟨hu, hf⟩ := units_off hpw i (μ := μ) (rd := rd) (cT := cT) (I := I) (L0 := L0) (ls0 := ls0)
      (own := fun s _ => Spike.Lib.X64.WakePh.ownG (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hq.toS.accs
    rw [hq.one, hf]; omega
  obtain ⟨e, he⟩ := hbx.term
  obtain ⟨w, hw, hw0⟩ := hbx.ev
  have hbq : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → q.1.a = .var "z" ∧ q.1.τ = .int ∧ q.1.ws = [w] := by
    intro q hq
    obtain ⟨_, ht⟩ := q.2.term; rw [hq, he] at ht
    obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
    have ha' := (Op.new.inj ha).1
    have hev := q.2.ev; rw [hq, ← ha', hw] at hev
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hev)
    exact ⟨ha'.symm, h1.symm, h2.symm⟩
  refine Spike.Lib.X64.WakePh.StartPlace.wake_start_wc_place hpw i hE hp hlo (fun _ h => h.2) hc0 hpl0 hax
    hs hro hC0 hfree hctr2 hcT ⟨rfl, rfl, rfl⟩ hP hti ?_ (Nat.le_refl _) (by rw [hh, hcl, ← hA]; omega)
    (by rw [hh, hcl]; omega) (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩)
    hoff
    (fun q hq => by rw [(hbq q hq).2.1, hf1, hu2]; omega)
    (fun q _ => mp_cellW hpw i q) (fun q hq => ⟨w, (hbq q hq).2.2, by rw [(hbq q hq).2.1]; rfl,
      by rw [hw0]; exact ⟨by decide, rfl⟩⟩) hWp hWs hxa
  refine ⟨⟨c0, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩,
    ⟨⟨.inr ⟨trivial, .var "z", [w], ⟨_, he⟩, hw, rfl⟩, hbx.hold, by show (1 : Nat) < 2 ^ 64; decide,
      Spike.Lib.X64.Rt.ArenaW.arOf_ctrLab hL .linux, Spike.Lib.X64.Rt.ArenaW.arOf_heapLab hL .linux,
      by rw [hh]; omega, rfl, by rw [hu2]; decide, by rw [hf1]; simp [Spike.Lib.X64.Alloc.mOf], hacc1, hrt0 _,
      mp_dataW hpw i hctrB,
      fun _ _ _ => hG _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        (.inr (by rw [hct, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact ⟨hc1, by omega⟩)) _,
      fun o' _ ho => ?_⟩, trivial, ⟨_, he⟩, hw, rfl⟩, rfl, rfl, rfl, rfl⟩
  have hd : Call.hdrAt (MS) ⟨c0, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩ o' =
      (Ly).Λ.heap.lo + 16 * o' := by simp [Call.hdrAt, hh, Spike.Lib.X64.Alloc.mOf]
  rw [hu2, hcl] at ho
  have hT : (BitVec.ofNat 64 (Call.hdrAt (MS) ⟨c0, "o", .var "z", .int, e, .int, [w], 1, 256#64, 0#64, 0#64⟩ o')).toNat
      = (Ly).Λ.heap.lo + 16 * o' := by rw [hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hrt0 _, mp_heapW hpw i fun k hk => ?_, hG _ (by omega) (.inl ?_) _⟩
  · rw [hT]; unfold Scc.Sem.Range.contains; omega
  · rw [hT]; unfold Scc.Sem.Range.contains; omega

end Spike.Lib.X64.WakePh.StartH0

/-- info: 'Spike.Lib.X64.WakePh.StartH0.mp_cellW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0.mp_cellW

/-- info: 'Spike.Lib.X64.WakePh.StartH0.wake_start_wc_h0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartH0.wake_start_wc_h0
