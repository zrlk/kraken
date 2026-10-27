/-
**`hello1.w` from `scc_rt_main`'s entry to its exits, the setup block's
source** (AArch64): cut A (`hello1_main_pre_segWS`,
`Spike/Lib/A64Hello1SetupPre.lean`) and cut B (`hello1_main_post_segWS`,
`Spike/Lib/A64Hello1SetupPost.lean`) composed, at the source of the start
before the setup block (`setupCall`), after the runtime's start
(`MainE`, `Spike/Lib/Rt/A64StartE.lean`).

At `scc_rt_main`'s entry the source is at `let r = call rodata u in e`
with no frame; the call and `rodata`'s first steps are taken there
(`setupCall_run`), so `wc_rodata` runs under the pushed frame
`setupFrame e env`. The allocator's return at `.sp0` continues into cut B
(`hret`, as `hello1_main_segW`'s); the heap abort is an exit at the frame,
`print`'s abort an exit with none.

- `SegWS.seq_or`: a segment, then another from one of its exits.
- `SetupPreP`, `SetupPostP`: cut A's and cut B's premises past the layout's.
- `rdJ'`: the source at `rodata`'s allocation, the entry's `sp` and thread
  pointer kept.
- `hello1_setup_main_segWS`: from `scc_rt_main`'s entry (`mainE0`) in any
  region of depth at least `288` to `print`'s abort or the heap abort.
- `hello1_setup_segWS`: the same after the runtime's start (`MainE`, the
  new stack's region of depth `L ≥ 288` for every value of its base): a
  segment from the start's entry `P0` to the exits, given the start's
  segment (`hD`, e.g. `startE_segWS`).
- `setupL`: `scc_rt_main`'s frame, `wc_rodata`'s need and the allocator's
  runtime depth (`80 + 48 + 208`), the depth the heap abort reaches.
-/
import Spike.Lib.A64Hello1SetupPost
import Spike.Lib.Rt.A64StartE

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk MainG mainN0 limA stackOff_stable)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Rt (MainE mainE0 swFSL swF_stableL)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Hello1RodataSrc (rdCN)

/-! ## Sequencing into one exit -/

namespace SegWS

variable {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide I} {P Q₁ Q₂ R : FragS I}

/-- **A segment, then another from one of its exits**: the other exits
stay. -/
theorem seq_or (h₁ : SegWS W K p lbl ms P (fun s c fs => Q₁ s c fs ∨ Q₂ s c fs)) (h₂ : SegWS W K p lbl ms Q₁ R) :
    SegWS W K p lbl ms P (fun s c fs => R s c fs ∨ Q₂ s c fs) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · obtain ⟨ho, hk⟩ := ho₁ s c fs h
    have hX : ∀ s c fs, (i₁ s c fs ∨ (Q₁ s c fs ∨ Q₂ s c fs)) →
        ((i₁ s c fs ∨ i₂ s c fs) ∨ (R s c fs ∨ Q₂ s c fs)) := fun s c fs h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr (hs₂ s c fs h))
      · exact .inr (.inr h)
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono hX, hk.mono hX⟩
  · obtain ⟨ho, hk⟩ := ho₂ s c fs h
    have hX : ∀ s c fs, (i₂ s c fs ∨ R s c fs) → ((i₁ s c fs ∨ i₂ s c fs) ∨ (R s c fs ∨ Q₂ s c fs)) :=
      fun s c fs h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)
    exact ⟨fun hK => (ho hK).mono fun s c fs h => h.mono hX, hk.mono hX⟩

end SegWS

/-! ## The premises -/

/-- **Cut A's premises** past the layout's (`hello1_main_pre_segWS`), at
the frames `fs1` and `rodata`'s allocation's invariant `J'`. -/
structure SetupPreP (W : FragS isaLSE2) (K : State → State → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs1 : List TermRun.Frame) (J' : AS → Ctl → Prop) : Prop where
  hW : MainPreW (fun s c => W s c fs1) K exe endPc R F (ms fs1) J'
  hlimM : ∀ σ c, J' σ c → LimOk (ms fs1) F exe endPc (tcbA σ.regs 8)
    (σ.regs.SP.toBitVec - (80 : Int64).toBitVec)
  hlimR : ∀ σ c, J' σ c → LimOk (ms fs1) F exe endPc (tcbA σ.regs 8)
    (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec)
  hq : ∀ σ c, J' σ c → ∃ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
    q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms fs1) = 3#64
  hmem : ∀ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
    (a = BitVec.ofNat 64 (ms fs1).ctr ∨
      ∃ o, o + (ms fs1).units q.n q.τ ≤ (ms fs1).cells ∧ a.toNat = q.hdrAt (ms fs1) o) →
    ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  hxa : ∀ m0 σC, ∀ q : AG (ms fs1) (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
    (∀ m, F' m → mF R F m0 σC m) →
    (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label
        (mRdJ0 (mNC (_root_.Executable.labels exe).label J').J σC) .call).J σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label (ms fs1) q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 0 mC m) →
    ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms fs1) q.1 l b w) s c →
      (ms fs1).xa l b w s c

/-- **Cut B's premises** past the layout's (`hello1_main_post_segWS`), for
the frame `fr` and a caller's state `m0`, `σC` at `wc_rodata`'s call. -/
structure SetupPostP (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (fr : TermRun.Frame) (m0 : MachineData) (σC : AS)
    (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  hW : MainPostSW W K exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ0.slot (-8))
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
    ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (rAddr σ0.regs .X0 i) 8 = none
  h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J1 σ0 { c with hold := some ((rAddr σ0.regs .X0 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 0).toNat ∧
    c.hold = some ((rAddr σ0.regs .X0 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J3 σ0 { c with hold := some ((rAddr σ0.regs .X0 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (rAddr σ0.regs .X0 8).toNat ∧
    c.hold = some ((rAddr σ0.regs .X0 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.X0.toBitVec = σ0.regs.X0.toBitVec →
    σ'.regs.X1.toBitVec = 0#64 → σ'.regs.X2.toBitVec = 2#64 → σ'.regs.X3.toBitVec = 13#64 →
    σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
    ∃ c', LocalRun p c c' ∧ retJ fr Jr σ' c'
  hlimW : ∀ σx c, Jr σx c →
    LimOk (ms []) F exe endPc (tcbA σx.regs 8) (σx.regs.SP.toBitVec - (96 : Int64).toBitVec)
  hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
    (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 0 m) ∧ CallerCells (wR R) (-96) (-48) 0 m) ∧
      Spike.Lib.A64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1") m) →
    ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".L19_wc_main.sp4").toBitVec →
    SegW (fun s c => W s c []) K p lbl (ms [])
      (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .svc))
      (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5))
  hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
    ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ k) →
    σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) →
    ∃ c', LocalRun p c c' ∧ Jw σ' c'
  hok : ∀ s c σx, Jw σx c →
    At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1" + 4 + 4 + 4, ⟨-80, []⟩,
      fun _ _ => True⟩ s c → SysOk p (ms []) s c (.exitGroup σx.regs.X0.toNat)

/-- **The source at `rodata`'s allocation**, `scc_rt_main`'s entry `sp`
and thread pointer kept (`mainN0`'s ghosts), `x0` the thread pointer
(`mainE0`). -/
-- `x0` is pinned: the setup frame's `me` must be placed (`PlacedS`), and `x0` is where it is.
def rdJ' (g : MainG) (σ : AS) (c : Ctl) : Prop :=
  c = rdCN ∧ σ.regs.SP.toBitVec = g.sp0 ∧ σ.regs.TPIDR_EL0 = g.tp ∧ σ.regs.X0.toBitVec = g.tp.toBitVec

/-- **The depth of the new stack's region after a setup block**:
`scc_rt_main`'s frame (`80`), `wc_rodata`'s need (`48`, `hello1Need`) and
the allocator's runtime depth (`208`, the heap abort's frame below its
own; `rtDepth`'s `alloc` row). -/
abbrev setupL : Int := 80 + 48 + 208

/-! ## From `scc_rt_main`'s entry -/

section Main

open Spike.Lib.Hello1Src (hello1Src)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from its entry at the setup block's source**: from
`mainE0` (the source at `setupCall e` in `env`, no frame) the call of
`rodata` and its first steps (`setupCall_run`), cut A at the frame
`setupFrame e env` (`hPre` at `rdJ'`), the allocator's return into cut B
(`hret`, `hPost`). Exits: `print`'s abort with no frame, the heap abort
under the frame. -/
theorem hello1_setup_main_segWS {W : FragS isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.A64.abi)
    {e : Expr} {env : TermRun.Env} (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {g : MainG} (hg : g.c0 = ⟨setupCall e, env, none⟩)
    {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hWe : ∀ s c, At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g) s c → W s c [])
    (hPre : SetupPreP W K lbl ms exe endPc R F [setupFrame e env] (rdJ' g))
    (hret : ∀ m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) .sp0).J σ c →
      Jp m0 σC σ c)
    (hPost : ∀ m0 σC, SetupPostP W K p lbl ms exe endPc R F (setupFrame e env) m0 σC (Jp m0 σC) (J1 m0 σC)
      (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) (Jr m0 σC) (Jw m0 σC)) :
    SegWS W K p lbl ms ((At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g)).at [])
      (fun s c fs => (At exe endPc R F (mAb (_root_.Executable.labels exe).label)).at [] s c fs ∨
        Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl
            (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' g)).J σC) .abort) s c) [setupFrame e env]
          s c fs) := by
  let lab := (_root_.Executable.labels exe).label
  have hA := hello1_main_pre_segWS (fs1 := [setupFrame e env]) hp hend hF hR hal hlo hhi
    (J := (mainE0 lab g).J) (J' := rdJ' g)
    (fun σ c ⟨⟨hc, hsp, htp⟩, hx⟩ => ⟨rdCN, hc ▸ hg ▸ setupCall_run hd hu, rfl, hsp, htp, hx⟩) hWe hPre.hW hPre.hlimM
    hPre.hlimR hPre.hq hPre.hmem hPre.hxa
  have hB : SegWS W K p lbl ms
      (fun s c fs => ∃ m0 σC, (At exe endPc (mR R) (mF R F m0 σC)
        (pN lab (Jp m0 σC) (J1 m0 σC) (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) .s0)).at [setupFrame e env] s c fs)
      ((At exe endPc R F (mAb lab)).at []) :=
    SegWS.exists_pre fun m0 => SegWS.exists_pre fun σC =>
      let h := hPost m0 σC
      hello1_main_post_segWS hp hend hF hR hal hlo hhi hK rfl h.hW h.hra h.hmem h.h1 h.h2 h.h3 h.h4 h.hedge
        h.hlimW h.hsvc h.hedgeW h.hok
  refine SegWS.seq_or (hA.mono_post ?_) hB
  rintro s c fs ⟨⟨m0, σC, y, h⟩, rfl⟩
  cases y
  · obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
    exact .inl ⟨m0, σC, ⟨he, hn, hdc, hpc, σ, hA, hD, hret m0 σC σ c hJ⟩, rfl⟩
  · exact .inr ⟨⟨m0, σC, h⟩, rfl⟩

end Main

/-! ## After the runtime's start -/

section Start

open Spike.Lib.Hello1Src (hello1Src)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}

/-- **`hello1.w` from the start's entry to `scc_rt_main`'s exits at the
setup block's source**: the start's segment to `MainE` (`hD`), then for
every value `v` of the new stack's base `hello1_setup_main_segWS` in its
region of depth `L ≥ 288` (`hL`; `setupL` for the heap abort's tail) under
`swFSL` (no write inside it breaks it: `hfit`, `hout`, `hfitS`). The
premises of cuts A and B are asked per `v` (`hPre`, `hret`, `hPost`). -/
theorem hello1_setup_segWS {W : FragS isaLSE2} {K : State → State → Prop} {P0 : FragS isaLSE2}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hL : 288 ≤ L) (hK : (ms []).K = some Scc.Sem.A64.abi)
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {e : Expr} {env : TermRun.Env} (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?) (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hD : SegWS W K p lbl ms P0 ((MainE exe endPc rS tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rS tcb top c0 L s c → W s c [])
    (hPre : ∀ v, SetupPreP W K lbl ms exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
      [setupFrame e env] (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩))
    (hret : ∀ v m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J σC) .sp0).J
        σ c → Jp v m0 σC σ c)
    (hPost : ∀ v m0 σC, SetupPostP W K p lbl ms exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) (setupFrame e env) m0 σC (Jp v m0 σC) (J1 v m0 σC)
      (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC)) :
    SegWS W K p lbl ms P0 (fun s c fs => ∃ v : BitVec 64,
      (At exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
        (mAb (_root_.Executable.labels exe).label)).at [] s c fs ∨
      Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR (swR v (-L) 0))
        (mF (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) m0 σC)
        (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl
          (mRdJ0 (mNC (_root_.Executable.labels exe).label (rdJ' ⟨top, UInt64.ofBitVec tcb, c0⟩)).J σC) .abort)
          s c) [setupFrame e env] s c fs) := by
  refine hD.seq ((SegWS.exists_pre (P := fun v : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK} =>
      (At exe endPc (swR v.1 (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v.1)
        (mainE0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩)).at [])
    fun v => (hello1_setup_main_segWS hp hend (fun m m' h hd' =>
        ⟨swF_stableL hfit hout m m' h.1 hd', stackOff_stable hfitS m m' h.2 hd'⟩) v.2.2 v.2.1
      (show -L ≤ -288 by omega) (Int.le_refl _) hK hd hu (g := ⟨top, UInt64.ofBitVec tcb, c0⟩) hc0
      (fun s c h => hWe s c ⟨v.1, v.2.1, v.2.2, h⟩) (hPre v.1) (hret v.1) (hPost v.1)).mono_post
      fun s c fs h => ⟨v.1, h⟩).mono_pre ?_)
  rintro s c fs ⟨⟨v, h16, hok, h⟩, rfl⟩
  exact ⟨⟨v, h16, hok⟩, h, rfl⟩

end Start

end Spike.Lib.A64.Flow.Hello1
