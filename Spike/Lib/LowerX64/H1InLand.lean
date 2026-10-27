/-
**`H1In` from the landings with their suspended frames** (x86-64; the twin
of `Spike/Lib/LowerA64/H1InLandA.lean`): the landings' states `El` of
`Closed2At`'s `H1In` taken as `LandStk` with the memory side `msOfAX` at a
fixed family, and each landing's segment inside `W2` over `IN … J` at the
placement extended by the landing's label from `landStk_seg`.

- `LandStk.fam`: a landing read at one family is one at any other
  (`msOfAX` differs between families only in `xa`, which `LandStk` does not
  read);
- `ElX`: the landings at the record's memory side at the family of all
  pairs;
- `H1OpenX`: the facts `landStk_seg` asks, at every family `J` containing
  the starts and every reachable placement: the newBuf element types
  (`hTn`), each context's region bound and `AllocStoreAt` in the body's
  rebased region `rbR R` (`hAW`), its `ResumeCx2` at the extended placement
  (`hres`), its aborts inside `Ab₀` (`hAb`), and the bottom frames' exits
  and the aborts ending (`hbot`, `hAbQ`);
- `h1In_ofLand`: `H1In` at `ElX` from `H1OpenX`;
- `in2X_ofLand`: `In2X` from `H0In` at `ElX` and `H1OpenX`.
-/
import Spike.Lib.LowerX64.H1Of2
import Spike.Lib.LowerX64.Closed2At

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

section Fam

variable {p : Prog} {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {ab : Option (State → Prop)} {own' : OwnS}

/-- **A landing at another family**: `msOfAX` at two families differs only
in its allocation fragment, which `LandStk` does not read, so a landing
read at the family `I0` is one at `I1`. -/
theorem LandStk.fam {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop}
    {I0 I1 : InvS} {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b w : Nat} {s : State} {c : Ctl}
    {fs : List TermRun.Frame}
    (hE : LandStk (p := p) hcode CxOk Bot (msOfAX Λ μ p rd G own' ar I0 ab) L ls l b w s c fs) :
    LandStk (p := p) hcode CxOk Bot (msOfAX Λ μ p rd G own' ar I1 ab) L ls l b w s c fs := by
  obtain ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, pcB, x, cn, τ, e, env, n, lits, cs, bufs, h, kv, u, la,
    zs, zc, kk, q, hcx, hra, hc0, hpt, hnb, hla, hzs, hcla, hbl, hpcB, hqra, hF', hctx, hAt, htp⟩ := hE
  have hq1 : q.1.OK (msOfAX Λ μ p rd G own' ar I1 ab L ls fs) (_root_.Executable.labels exe).label := by
    have h := q.2
    cases ab <;>
      exact ⟨h.term, h.ev, h.num, h.hold, h.n_lt, h.ctr, h.heap, h.room, h.cells, h.units, h.off, h.accs, h.rt,
        h.mp, h.grow, h.hdr⟩
  refine ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, pcB, x, cn, τ, e, env, n, lits, cs, bufs, h, kv, u, la,
    zs, zc, kk, ⟨q.1, hq1⟩, hcx, hra, hc0, hpt, hnb, hla, hzs, hcla, hbl, hpcB, hqra, hF', fun m hm => ?_, ?_, htp⟩
  · have h := hctx m hm
    cases ab <;> exact h
  · cases ab <;> exact hAt

end Fam

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

/-- **The landings' states** at the record: `LandStk` at the rows' memory
side at the family of all pairs (any fixed family serves, `LandStk.fam`). -/
def ElX (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) (Bot : StkKey → List TermRun.Frame → Prop) :
    Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  fun L ls l b w => LandStk (p := p) hcode CxOk Bot (fun L ls => MSR (fun _ _ _ _ _ => True) L ls) L ls l b w

/-- **The facts `landStk_seg` asks at the record** for the landings `ElX`
and the write tail `Dt`, at every family `J` containing the starts
(`StartsSX` at `ElX`) and every reachable placement `L`, `ls` with a fresh
label `l` the arena hands out at `b` with `n` words: the newBuf element
types (`hTn`); each context's region bound and `AllocStoreAt` at `L`, `ls` in
the body's rebased region `rbR R` (`hAW`); its `ResumeCx2` at the extended
placement (`hres`); its aborts inside `Ab₀` (`hAb`); the bottom frames'
exits (`hbot`) and `Ab₀` (`hAbQ`) ending nowhere. -/
structure H1OpenX (E : Entry) (hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d)
    (CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop) (Bot : StkKey → List TermRun.Frame → Prop) (Dt : State → Prop)
    (Ab₀ : FragS isa) : Prop where
  /-- The allocations' element types take a word each (at the compiled blocks). -/
  hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true
  /-- Each context's rebased region below the allocator's frame and its allocations' stores. -/
  hAW : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (rtF (Ly)) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (rbR R).lo ≤ -Spike.Lib.X64.Flow.NewBuf.allocAbortDepth ((hcode j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).fr (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT exe endPc (rbR R) F ((MSR J L ls) fs) fp ra tp G0 i (T j)
        (RetLk d.retTy)
  /-- Each context's `ResumeCx2` at the extended placement. -/
  hres : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (rtF (Ly)) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
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
      ∀ s c fs, StartsSX h E (rtF (Ly)) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
    ∀ k fs, Bot k fs →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n))
        (ExitStk p P (Spike.Lib.AllocReach.upd L l b) exe endPc k fs Ab₀) fun _ _ _ => False
  /-- The aborts end nowhere. -/
  hAbQ : ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (rtF (Ly)) (ElX h hcode CxOk Bot) Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs) →
    ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
      Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      SegWS (W2R J Dt (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) KT p
        (Spike.Lib.AllocReach.upd L l b)
        (MSR J (Spike.Lib.AllocReach.upd L l b) (Spike.Lib.AllocReach.updN ls l n)) Ab₀ fun _ _ _ => False

/-- **`H1In` from the landings** (`landStk_seg` at `W2R`, `MSR` and
`Q := False`, the landing moved from the fixed family to `J` by
`LandStk.fam`; the label without size at a reachable placement by
`Reach.lsize_none`). -/
theorem h1In_ofLand {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Ab₀ : FragS isa} (H : H1OpenX h E hcode CxOk Bot Dt Ab₀) :
    H1In h E (ElX h hcode CxOk Bot) Dt := by
  refine ⟨fun J hJ L ls l b n hR hl hAL => ?_⟩
  have hz : ls l = 0 := Spike.Lib.LowerNode.Reach.lsize_none (fun _ _ => rfl) hR l hl
  exact (landStk_seg (W := fun L ls => W2R J Dt L ls) (K := KT) (ms := fun L ls => MSR J L ls)
    (Ab₀ := Ab₀) (Q := fun _ _ _ => False) hl hz H.hTn (H.hAW J hJ L ls hR)
    (H.hres J hJ L ls l b n hR hl hAL) H.hAb (H.hbot J hJ L ls l b n hR hl hAL)
    (H.hAbQ J hJ L ls l b n hR hl hAL)).mono_pre fun _ _ _ hE => LandStk.fam hE

/-- **`In2X` from the start's segment at the landings `ElX`**
(`h1In_ofLand`): the start's side proved at the same code `hcode`,
contexts `CxOk` and bottoms `Bot` the landings carry, so its allocator
calls' `xa` comes from `landStk_hxa` at `ElX`'s family. -/
theorem in2X_ofLand {E : Entry}
    {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
    {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop}
    {Ab₀ : FragS isa} (H0 : H0In h E (ElX h hcode CxOk Bot) Dt) (H : H1OpenX h E hcode CxOk Bot Dt Ab₀) :
    In2X h E :=
  ⟨_, Dt, H0, h1In_ofLand h H⟩

end In

/-- info: 'Spike.Lib.LowerX64.LandStk.fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LandStk.fam

/-- info: 'Spike.Lib.LowerX64.h1In_ofLand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h1In_ofLand

/-- info: 'Spike.Lib.LowerX64.in2X_ofLand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2X_ofLand

end Spike.Lib.LowerX64
