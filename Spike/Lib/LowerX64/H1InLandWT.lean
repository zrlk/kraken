/-
**The landings' open premises on the walk past the landed allocations**
(x86-64; b1): `H1OpenXW`, `h1InW_ofLand`, `in2XW_ofLand`
(`Spike/Lib/LowerX64/H1InLandW.lean`) and `H1RestXW`, `H1RestXW.toOpen`
(`Spike/Lib/LowerX64/H1RestXW.lean`) with each context's `ResumeCx2` at the
extended placement split as `landStk_segT` takes it
(`Spike/Lib/LowerX64/ResumeCx2T.lean`): the landing's context's
`ResumeCx2T` at a restriction `Tr j` (`hresL`), `Tr` closed under the
landed continuations' tails (`hTr`), the records' contexts' `ResumeCx2` at
a call (`hresS`). `hAW` is `H1OpenXW`'s, byte for byte.

- `H1OpenXWT`, `h1InW_ofLandT`, `in2XW_ofLandT`;
- `H1RestXWT`, `H1RestXWT.toOpen`.

**Why the walk restriction** (the decision behind b1): `H1RestXW.hres` asks
each context's full `ResumeCx2` at the landing's extended placement
`upd L l b`, `updN ls l n`, so its `CxLB.hAW`, i.e. `AllocW2At` there (with
`NewBufC` at the landed allocation itself). That is **unsatisfiable once a
label is placed**: `AllocW2`'s `hsz` asks every call `q` the allocator's
`q.OK` admits to fit the label it returns; with one placed 1-word label
`l1` at `b1` = the heap's `16 * old0 + 8 * (2 * mOf h) + 8` and `q.n = 2`
(`rodata`'s call), `q.OK` still holds (the header's `rt` addresses miss
`l1`'s 8-byte window) and `hsz` asks `2 ≤ 1`. `Call.OK.hdr` (over every
offset) fails likewise once a label of ≥ 2 words is placed. `H1RestXWT`
asks the landing's context only at the walk's points after the landed
allocation (`ResumeCx2T` at `Tr`), where `rodata` has no allocation, so
`CxLB`'s allocation fields hold vacuously there.
-/
import Spike.Lib.LowerX64.H1GX
import Spike.Lib.LowerX64.ResumeCx2T

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Rt (rtF)

section In

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates (as in `Closed2At`). -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in `Closed2At`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (as in `Closed2At`). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (Spike.Lib.X64.Rt.rS0 (Ly))

/-- **`H1OpenXW` on the walk past the landed allocations** (`landStk_segT`'s
premises): `H1OpenXW` with its contexts' `ResumeCx2` (`hres`) split into
the landing's context's `ResumeCx2T` at `Tr j` (`hresL`), the restriction
closed under the landed continuations' tails (`hTr`) and the records'
contexts' `ResumeCx2` at a call (`hresS`). -/
structure H1OpenXWT (E : Entry) (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) (Bot : StkKey → List TermRun.Frame → Prop) (Dt : State → Prop)
    (Ab₀ : FragS isa) (Tr : Nat → Expr → Prop) : Prop where
  /-- The allocations' element types take a word each (at the compiled blocks). -/
  hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true
  /-- Each context's rebased region below the allocator's frame and its allocations' stores. -/
  hAW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (rbR R).lo ≤ -Spike.Lib.X64.Flow.NewBuf.allocAbortDepth ((hcode j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).fr (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT exe endPc (rbR R) F ((MSR J L ls) fs) fp ra tp G0 i (T j)
        (RetLk d.retTy)
  /-- The restriction holds at the tails of the landed allocations' continuations. -/
  hTr : ∀ j d, P[j]? = some d → ∀ x cn τ e t, T j (.let_ x (.newBuf cn τ) e) → TailOf t e → Tr j t
  /-- Each context's `ResumeCx2T` at the extended placement (the landing's context). -/
  hresL : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ResumeCx2T (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (hcode j d hd) R F fs fp ra tp G0 Ab (Tr j)
  /-- Each context's `ResumeCx2` at the extended placement at a call (the records' contexts). -/
  hresS : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (∃ x g b e, T j (.let_ x (.call g [] b []) e)) →
      ResumeCx2 (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (hcode j d hd) R F fs fp ra tp G0 Ab
  /-- Each context's aborts inside `Ab₀`. -/
  hAb : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → Ab₀ s c fs'
  /-- The bottom frames' exits end nowhere. -/
  hbot : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ k fs, Bot k fs →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (ExitStk p P (Spike.Lib.AllocReach.upd L l b) exe endPc k fs Ab₀) fun _ _ _ => False
  /-- The aborts end nowhere. -/
  hAbQ : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) Ab₀ fun _ _ _ => False

/-- **`H1InW` from the landings on the walk past the landed allocations**
(`h1InW_ofLand` at `landStk_segT`: `W2R`, `MSR` and `Q := False`, the
landing moved from the fixed family to `J` by `LandStk.fam`; the label
without size at a reachable placement by `Reach.lsize_none`). -/
theorem h1InW_ofLandT {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Ab₀ : FragS isa} {Tr : Nat → Expr → Prop} (H : H1OpenXWT h E hcode CxOk Bot Dt Ab₀ Tr) :
    H1InW h E (ElX h hcode CxOk Bot) Dt := by
  refine ⟨fun J hJ L ls l b n hR hl hAL => ?_⟩
  have hz : ls l = 0 := Spike.Lib.LowerNode.Reach.lsize_none (fun _ _ => rfl) hR l hl
  exact (landStk_segT (W := fun L ls => W2R J Dt L ls) (K := KT) (ms := fun L ls => MSR J L ls)
    (Ab₀ := Ab₀) (Q := fun _ _ _ => False) hl hz H.hTn (H.hAW J hJ L ls hR) H.hTr
    (H.hresL J hJ L ls l b n hR hl hAL) (H.hresS J hJ L ls l b n hR hl hAL) H.hAb
    (H.hbot J hJ L ls l b n hR hl hAL)
    (H.hAbQ J hJ L ls l b n hR hl hAL)).mono_pre fun _ _ _ hE => LandStk.fam hE

/-- **`In2XW` from the start's segment at the landings `ElX`, on the walk
past the landed allocations** (`in2XW_ofLand` at `h1InW_ofLandT`): the
start's side proved at the same code `hcode`, contexts `CxOk` and bottoms
`Bot` the landings carry. -/
theorem in2XW_ofLandT {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Ab₀ : FragS isa} (H0 : H0InW h E (ElX h hcode CxOk Bot) Dt) {Tr : Nat → Expr → Prop}
    (H : H1OpenXWT h E hcode CxOk Bot Dt Ab₀ Tr) :
    In2XW h E :=
  ⟨_, Dt, H0, h1InW_ofLandT h H⟩

/-- **`H1OpenXWT`'s premises but `hTn`, `hAb` and `hAbQ`**, at the
contexts' aborts gathered (`GX`; `H1RestXW` with `hres` split as in
`H1OpenXWT`): each context's region bound and `AllocStoreAt` at `L`, `ls`
(`hAW`), the restriction's closure (`hTr`), the landing's context's
`ResumeCx2T` (`hresL`) and the records' contexts' `ResumeCx2` at a call
(`hresS`) at the extended placement, the bottom frames' exits ending
nowhere (`hbot`). -/
structure H1RestXWT (E : Entry) (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) (Bot : StkKey → List TermRun.Frame → Prop) (Dt : State → Prop)
    (Tr : Nat → Expr → Prop) : Prop where
  /-- Each context's rebased region below the allocator's frame and its allocations' stores. -/
  hAW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (rbR R).lo ≤ -Spike.Lib.X64.Flow.NewBuf.allocAbortDepth ((hcode j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).fr (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT exe endPc (rbR R) F ((MSR J L ls) fs) fp ra tp G0 i (T j)
        (RetLk d.retTy)
  /-- The restriction holds at the tails of the landed allocations' continuations. -/
  hTr : ∀ j d, P[j]? = some d → ∀ x cn τ e t, T j (.let_ x (.newBuf cn τ) e) → TailOf t e → Tr j t
  /-- Each context's `ResumeCx2T` at the extended placement (the landing's context). -/
  hresL : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ResumeCx2T (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (hcode j d hd) R F fs fp ra tp G0 Ab (Tr j)
  /-- Each context's `ResumeCx2` at the extended placement at a call (the records' contexts). -/
  hresS : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (∃ x g b e, T j (.let_ x (.call g [] b []) e)) →
      ResumeCx2 (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (hcode j d hd) R F fs fp ra tp G0 Ab
  /-- The bottom frames' exits end nowhere. -/
  hbot : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ k fs, Bot k fs →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (ExitStk p P (Spike.Lib.AllocReach.upd L l b) exe endPc k fs (GX CxOk)) fun _ _ _ => False

omit [Kraken.Executable.ValidLayout exe] in
/-- **`H1OpenXWT` at the contexts' aborts gathered** from `H1RestXWT`, the
element types (`hTn`) and the aborts ending nowhere (`hAbQ`); `hAb` by
construction (`gx_hAb`). -/
theorem H1RestXWT.toOpen {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Tr : Nat → Expr → Prop} (H : H1RestXWT h E hcode CxOk Bot Dt Tr)
    (hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hAbQ : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
        SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
          (Spike.Lib.AllocReach.upd L l b)
          (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) (GX CxOk)
          fun _ _ _ => False) :
    H1OpenXWT h E hcode CxOk Bot Dt (GX CxOk) Tr :=
  ⟨hTn, H.hAW, H.hTr, H.hresL, H.hresS, gx_hAb, H.hbot, hAbQ⟩

end In

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.h1InW_ofLandT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h1InW_ofLandT

/-- info: 'Spike.Lib.LowerX64.in2XW_ofLandT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.in2XW_ofLandT

/--
info: 'Spike.Lib.LowerX64.H1RestXWT.toOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.H1RestXWT.toOpen
