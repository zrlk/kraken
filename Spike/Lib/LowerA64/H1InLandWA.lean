/-
**`H1InAW` from the landings with their suspended frames** (AArch64; the
twin of `Spike/Lib/LowerX64/H1InLandW.lean`): `H1InLandA`'s `H1OpenA`,
`h1InA_ofLand`, `in2A_ofLand` at the start's frame condition `WordsNone ∧
rtF` (`WNF`, `Closed2AtWA`'s `H1InAW`, `In2AW`): the frame invariant `J`
holding at the starts at `WNF`.

- `H1OpenAW`: `H1OpenA` with `StartsSA` at `WNF`;
- `h1InAW_ofLand`: `H1InAW` at `ElA` from `H1OpenAW`;
- `in2AW_ofLand`: `In2AW` from `H0InAW` at `ElA` and `H1OpenAW`.
-/
import Spike.Lib.LowerA64.H1InLandA
import Spike.Lib.LowerA64.Closed2AtWA

namespace Spike.Lib.LowerA64


open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Rt (rtF)


section In

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates (as in `Closed2AtA`). -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.A64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in `Closed2AtA`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly))
    (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (as in `Closed2AtA`). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))

set_option hygiene false in
/-- The start's frame condition: the private memory loading no runtime word and `rtF`. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m


/-- **`H1OpenA` at `WordsNone ∧ rtF`** (`WNF`): the facts `landStk_seg` asks at the record for the landings `ElA`
and the write tail `Dt`, at every family `J` containing the starts
(`StartsSA` at `ElA`) and every reachable placement `L`, `ls` with a fresh
label `l` the arena hands out at `b` with `n` words: the newBuf element
types (`hTn`); each context's region bound and `AllocStoreAt` at `L`, `ls`
(`hAW`); its `ResumeCx2` at the extended placement (`hres`); its aborts
inside `Ab₀` (`hAb`); the bottom frames' exits (`hbot`) and `Ab₀` (`hAbQ`)
ending nowhere. -/
structure H1OpenAW (E : Entry) (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop) (Bot : StkKey → List TermRun.Frame → Prop) (Dt : State → Prop)
    (Ab₀ : FragS isaLSE2) : Prop where
  /-- The allocations' element types (in the program's bodies) take a word each. -/
  hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true
  /-- Each context's region below the allocator's frame and the returned base's store (`AllocStoreAt`). -/
  hAW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (WNF) (ElA h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      R.lo ≤ -Spike.Lib.A64.Flow.NewBuf.allocAbortDepth ((hcode j d hd).cx.frame : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).cx (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT exe endPc R F ((MSR J L ls) fs) fp ra tp G0 i (T j)
        (RetLk d.retTy)
  /-- Each context's `ResumeCx2` at the extended placement. -/
  hres : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (WNF) (ElA h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ResumeCx2 (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (hcode j d hd) R F fs fp ra tp G0 Ab
  /-- Each context's aborts inside `Ab₀`. -/
  hAb : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → Ab₀ s c fs'
  /-- The bottom frames' exits end nowhere. -/
  hbot : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (WNF) (ElA h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ k fs, Bot k fs →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (ExitStk p P (Spike.Lib.AllocReach.upd L l b) exe endPc k fs Ab₀) fun _ _ _ => False
  /-- The aborts end nowhere. -/
  hAbQ : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSA h E (WNF) (ElA h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) Ab₀ fun _ _ _ => False

/-- **`H1InAW` from the landings** (`h1InA_ofLand` at `WNF`: `landStk_seg` at `W2R`, `MSR` and
`Q := False`, the landing moved from the fixed family to `J` by
`LandStk.fam`; the label without size at a reachable placement by
`Reach.lsize_none`). -/
theorem h1InAW_ofLand {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Ab₀ : FragS isaLSE2} (H : H1OpenAW h E hcode CxOk Bot Dt Ab₀) :
    H1InAW h E (ElA h hcode CxOk Bot) Dt := by
  refine ⟨fun J hJ L ls l b n hR hl hAL => ?_⟩
  have hz : ls l = 0 := Spike.Lib.LowerNode.Reach.lsize_none (fun _ _ => rfl) hR l hl
  exact (landStk_seg (W := fun L ls => W2R J Dt L ls) (K := KT) (ms := fun L ls => MSR J L ls)
    (Ab₀ := Ab₀) (Q := fun _ _ _ => False) hl hz H.hTn (H.hAW J hJ L ls hR)
    (H.hres J hJ L ls l b n hR hl hAL) H.hAb (H.hbot J hJ L ls l b n hR hl hAL)
    (H.hAbQ J hJ L ls l b n hR hl hAL)).mono_pre fun _ _ _ hE => LandStk.fam hE

/-- **`In2AW` from the start's segment at the landings `ElA`**
(`h1InAW_ofLand`; `in2A_ofLand` at `WNF`): the start's side proved at the same code `hcode`,
contexts `CxOk` and bottoms `Bot` the landings carry, so its allocator
calls' `xa` comes from `landStk_hxa` at `ElA`'s family. -/
theorem in2AW_ofLand {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Ab₀ : FragS isaLSE2} (H0 : H0InAW h E (ElA h hcode CxOk Bot) Dt) (H : H1OpenAW h E hcode CxOk Bot Dt Ab₀) :
    In2AW h E :=
  ⟨_, Dt, H0, h1InAW_ofLand h H⟩


end In

/-- info: 'Spike.Lib.LowerA64.h1InAW_ofLand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h1InAW_ofLand

/-- info: 'Spike.Lib.LowerA64.in2AW_ofLand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2AW_ofLand

end Spike.Lib.LowerA64
