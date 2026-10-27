/-
**The x86-64 `Accepted2` segment obligations at the start's frame
condition `WordsNone ∧ rtF`** (the twins of `H0In`, `H1In`, `In2X`,
`rest2X_ofIn`, `Spike/Lib/LowerX64/Closed2At.lean`): the start's states
`S0X` and the starts `StartsSX` at the frame condition `WNF`, the entry's
memory loading no heap or image word (`WordsNone`, the entry stack clear of
the layout) besides the runtime's words unloaded (`rtF`). The start's
segment may then carry `WordsNone` to the setup block's and the user
function's frame conditions.

- `entry_atXECW`: `entry_atXEC` under `WordsNone ∧ rtF`
  (`wordsNone_stackMem`);
- `hst2X_ofW`: `hst2X_of` from `WordsNone ∧ rtF`;
- `rest2X_ofW`: `rest2X_of'` at `FE := WordsNone ∧ rtF`
  (`nodes2_of_startsS`, `hst2X_ofW`), no change to `Open2X`;
- `H0InW`, `H1InW`, `In2XW`, `rest2X_ofInW`: `H0In`, `H1In`, `In2X`,
  `rest2X_ofIn` at `WNF`;
- `x64_scc_correctE_text_closedAt2_atW`, `Closed2InW`,
  `x64_scc_correctE_text_closedAt2W`: `Closed2Stmt` from `In2XW` at every
  instance.
-/
import Spike.Lib.LowerX64.Closed2At
import Spike.Lib.X64DmemPrivPlace

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Rt (RuntimeLayout rtF entryR)

/-- **The loaded thread at `_start`'s node with the control `c` under
`WordsNone ∧ rtF`** (`entry_atXEC`): the entry state's memory loads no heap
or image word (`wordsNone_stackMem`). -/
theorem entry_atXECW {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
    (h : placeOKAt pcfg Λ o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) (c : Ctl) {E : Entry}
    (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    Spike.Lib.X64.At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (fun m => Spike.Lib.DmemPriv.WordsNone (RuntimeLayout.ofPlaceOK h i).Λ m.dmem ∧
        rtF (RuntimeLayout.ofPlaceOK h i) m)
      (Spike.Lib.X64.Rt.entryN0 (RuntimeLayout.ofPlaceOK h i).lab c)
      (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) c := by
  obtain ⟨a1, a2, a3, a4, σ, hA, hF, hJ⟩ := entry_atXEC h i c hE hpc
  exact ⟨a1, a2, a3, a4, σ, hA, ⟨Spike.Lib.X64DmemPriv.wordsNone_stackMem (wf_link_of_placeOKAt i h) hE.1, hF⟩, hJ⟩

section In

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- **`W2` at the record** (as in `Spike/Lib/LowerX64/Closed2At.lean`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab`. -/
local notation "MSR" J:max ab:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) ab L ls

/-- **`hst2X_of` from `WordsNone ∧ rtF`**: the loaded thread in `IN … inv`
for any family `inv` containing the start's fragment at a frame condition
`FE` that `WordsNone ∧ rtF` implies (`entry_atXECW`). -/
theorem hst2X_ofW {E : Entry} (hE : E.Ok (lay2 Λ p)) {ar : Arena} {inv : InvS}
    {FE : MachineData → Prop} (hF : ∀ m, Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem → rtF (Ly) m → FE m)
    {c0 : Ctl}
    (hS0 : ∀ s c fs, (Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE
      (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [] s c fs → inv (fun _ => none) (fun _ => 0) s c fs) :
    IN ar (fun _ => none) (fun _ => 0) inv (lay2 Λ p).static (fun _ => 0)
      (threadAt E (lay2 Λ p).code.lo o.prog (loadSyms (lay2 Λ p) o.secs.rodata)) c0 [] := by
  refine ⟨Reach.base, hS0 _ _ _ ⟨?_, rfl⟩⟩
  obtain ⟨h1, h2, h3, h4, σ, hA, hR, hJ⟩ :=
    entry_atXECW h _ c0 hE (Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h _ E)
  exact ⟨h1, h2, h3, h4, σ, hA, hF _ hR.1 hR.2, hJ⟩

/-- **`Rest2X` from the segments at the frame condition `WordsNone ∧ rtF`**
(`rest2X_of` with `hst2X_ofW` in place of `hst2X_of`): left open, the
start's and the landings' segments (`h0`, `h1`) and `hpr`. -/
theorem rest2X_ofW {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λ p))
    {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    {ab : Option (State → Prop)}
    (h0 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) El Dt ab L ls s c fs → J L ls s c fs) →
      SegWS (W2R J Dt (fun _ => none) (fun _ => 0))
        (TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) p (fun _ => none)
        (MSR J ab (fun _ => none) (fun _ => 0)) (S0X h E (WNF)) fun _ _ _ => False)
    (h1 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSX h E (WNF) El Dt ab L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
        SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
          (TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) p
          (Spike.Lib.AllocReach.upd L l b)
          (MSR J ab (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
          (El L ls l b n) fun _ _ _ => False)
    (hpr : ab = none ∨
      (ab = some (Spike.Lib.X64.WriteAb.Ab (Ly).lab) ∧
        Scc.Lower.hasPrint p = true)) :
    Rest2X (lay2 Λ p) p h arch E := by
  obtain ⟨inv, hP, hN, hT, hA, -, h1s⟩ := nodes2_of_startsS (Q := SrcSem.srcP1o arch p) h0 h1
    (Spike.Lib.X64.PhRec.site_ofPlaceOK h _)
  refine ⟨_, _, _, _, ab, hst2X_ofW h hE (fun _ h1 h2 => ⟨h1, h2⟩) hP, hN, ?_, hT, htk0X_2 h E, hA,
    hab0X_2 h E⟩
  rcases hpr with hn | ⟨rfl, hx⟩
  · exact .inl hn
  · exact .inr ⟨rfl, hx, h1s⟩

/-- **`H0In` at the start's frame condition `WordsNone ∧ rtF`**: from
`_start`'s node on the entry stack (`S0X` at `WNF`) inside `W2` over
`IN … J` for every frame invariant `J` holding at the starts (`StartsSX`
at `WNF`). -/
structure H0InW (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop where
  /-- The start's segment inside `W2` over `IN … J`. -/
  h0 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    SegWS (W2R J Dt (fun _ => none) (fun _ => 0))
      (TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) p (fun _ => none)
      (MSR J (ab2 p (Ly).lab) (fun _ => none) (fun _ => 0)) (S0X h E (WNF)) fun _ _ _ => False

/-- **`H1In` at the start's frame condition `WordsNone ∧ rtF`**: each
landing's segment, the frame invariant `J` holding at the starts at
`WNF`. -/
structure H1InW (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop where
  /-- Each landing's segment inside `W2` over `IN … J`. -/
  h1 : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))) p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (ab2 p (Ly).lab) (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (El L ls l b n) fun _ _ _ => False

/-- **The segment obligations at `WordsNone ∧ rtF`**: some landings'
states `El` and write tail `Dt` with `H0InW` and `H1InW`. -/
def In2XW (E : Entry) : Prop :=
  ∃ (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop),
    H0InW h E El Dt ∧ H1InW h E El Dt

/-- **`Rest2X` from `In2XW`** (`rest2X_ofW` at `ab2`, `hpr2`). -/
theorem rest2X_ofInW {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λ p)) (H : In2XW h E) :
    Rest2X (lay2 Λ p) p h arch E := by
  obtain ⟨El, Dt, H0, H1⟩ := H
  exact rest2X_ofW h hE H0.h0 H1.h1 (hpr2 p _)

end In

open Scc.Cert.Link.X64 in
/-- **`x64_scc_correctE_text_closedAt2_at` from `In2XW`** (`rest2X_ofInW` in
place of `rest2X_ofIn`). -/
theorem x64_scc_correctE_text_closedAt2_atW {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (hp : Scc.Lower.Accepted2 p = true) (_hR : Scc.Lower.mainRetOk p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (_hcfg : CfgNeedOk pcfg = true)
    (H : ∀ E : Entry, E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
      In2XW h' E)
    {text : String} (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩ := by
  intro E hE
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hpa
  exact correct_of_parsed _ E h1 h2
    (correct2_of hp h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h) hB hE
      (hnum2 hp h arch) (hd2 hp h) (hrd2 hp h arch) (rest2X_ofInW h hE (H E hE h)))

/-- **The segment obligations of the `Accepted2` theorem at
`WordsNone ∧ rtF`**: `In2XW` at every instance of `Closed2Stmt` and every
admissible entry state. -/
def Closed2InW : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    In2XW h' E

/-- **`Closed2Stmt` from `Closed2InW`**
(`x64_scc_correctE_text_closedAt2_atW` at each instance). -/
theorem x64_scc_correctE_text_closedAt2W (H : Closed2InW) : Closed2Stmt := by
  intro cfg pcfg p sizes labelOffs Λ hp hR h hcfg text hpa B hB arch
  exact x64_scc_correctE_text_closedAt2_atW hp hR h hcfg (H cfg pcfg p sizes labelOffs Λ hp hR h hcfg) hpa hB

/-- info: 'Spike.Lib.LowerX64.rest2X_ofInW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rest2X_ofInW

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt2W' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closedAt2W

end Spike.Lib.LowerX64
