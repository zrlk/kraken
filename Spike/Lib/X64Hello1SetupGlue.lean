/-
**`hello1.w` from `scc_rt_main`'s entry to its exits, the setup block's
source** (x86-64): cut A (`hello1_main_pre_segWS`,
`Spike/Lib/X64Hello1SetupPre.lean`) and cut B (`hello1_main_post_segWS`,
`Spike/Lib/X64Hello1SetupPost.lean`) composed, at the source of the start
before the setup block (`setupCall`), after the runtime's start
(`MainE`, `Spike/Lib/Rt/X64StartE.lean`). The x86-64 twin of
`Spike/Lib/A64Hello1SetupGlue.lean`.

At `scc_rt_main`'s entry the source is at `let r = call rodata u in e`
with no frame; the call and `rodata`'s first steps are taken there
(`setupCall_run`), so `wc_rodata` runs under the pushed frame
`setupFrame e env`. The allocator's return at `.x13` continues into cut B
(`hret`, as `hello1_main_segW`'s); the heap abort is an exit at the frame,
`print`'s abort an exit with none.

- `SegWS.seq_or`: a segment, then another from one of its exits.
- `SetupPreP`, `SetupPostP`: cut A's and cut B's premises past the layout's.
- `rdJ'`: the source at `rodata`'s allocation, the entry's `%rsp` and
  thread pointer kept.
- `hello1_setup_main_segWS`: from `scc_rt_main`'s entry (`mainE0`) in any
  region of depth at least `288` to `print`'s abort or the heap abort.
- `hello1_setup_segWS`: the same after the runtime's start (`MainE`, the
  callee's region of `call scc_rt_main` in the new stack's region of depth
  `L ≥ 296`, for every value of its base): a segment from the start's entry
  `P0` to the exits, given the start's segment (`hD`, e.g.
  `startE_segWS`).
- `setupL`: `scc_rt_main`'s frame down to `wc_rodata`'s return address
  (`80`), `wc_rodata`'s and the allocator's depth below it (`208`,
  `allocAbortDepth 40`) and the heap abort's dispatcher (`32`), the depth
  of `scc_rt_main`'s region the heap abort reaches.

Where x86-64 differs from AArch64: `scc_rt_main`'s region after the start
is `call scc_rt_main`'s callee region (`MainE`, its region and frame
condition from `mainE_ok`), so the start's depth is `L ≥ 296` (`8` more than
`scc_rt_main`'s `288`) and `8 ∣ L`; there is no alignment premise; the
premise structures carry x86-64's (`%rsp`/`%fs` base in the limit words,
`%rbp`'s offset at the returns: `hbp`, `hbpr`, `hbpw`); the allocator's
return is at `.x13` (`rdX13`); `setupL` is x86-64's (`80 + 208 + 32`).
-/
import Spike.Lib.X64Hello1SetupPost
import Spike.Lib.Rt.X64StartE

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk MainG mainN0 limA tpOf)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.Rt (MainE mainE0 swFSL mainE_ok)
open Scc.Cert.Rt.X64 (Lays endOf)
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
structure SetupPreP (W : FragS isa) (K : State → State → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs1 : List TermRun.Frame) (J' : AS → Ctl → Prop) : Prop where
  hW : MainPreW (fun s c => W s c fs1) K exe endPc R F (ms fs1) J'
  hlimM : ∀ σ c, J' σ c → LimOk (ms fs1) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
    (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec)
  hlimR : ∀ σ c, J' σ c → LimOk (ms fs1) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
    (σ.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec)
  hq : ∀ σ c, J' σ c → ∃ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
    q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms fs1) = 3#64
  hmem : ∀ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
    (a = BitVec.ofNat 64 (ms fs1).ctr ∨
      ∃ o, o + (ms fs1).units q.n q.τ ≤ (ms fs1).cells ∧ a.toNat = q.hdrAt (ms fs1) o) →
    ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  hxa : ∀ m0 σC, ∀ q : AG (ms fs1) (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
    (∀ m, F' m → mF R F m0 σC m) →
    (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R J').J σC) .call).J σ c ∧
      (Alloc.N (_root_.Executable.labels exe).label (ms fs1) q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 8 mC m) →
    ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms fs1) q.1 l b w) s c →
      (ms fs1).xa l b w s c

/-- **Cut B's premises** past the layout's (`hello1_main_post_segWS`), for
the frame `fr` and a caller's state `m0`, `σC` at `wc_rodata`'s call. -/
structure SetupPostP (W : FragS isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (fr : TermRun.Frame) (m0 : MachineData) (σC : AS)
    (Jp J1 J2 J3 J4 Jr Jw : AS → Ctl → Prop) : Prop where
  hW : MainPostSW W K exe endPc R F ms fr m0 σC Jp J1 J2 J3 J4 Jr Jw
  hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8)
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x2" = Int64.ofBitVec (σ0.slot 0)
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
    ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none
  h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
    c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  h3 : ∀ σ0 c, J2 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
    c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hedge : ∀ σ0 c, J4 σ0 c → ∀ σ' : AS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
    σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
    σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
    ∃ c', LocalRun p c c' ∧ retJ fr Jr σ' c'
  hbpr : ∀ σx c, Jr σx c → σx.regs.get64 .rbp = R.addr (-8)
  hlimW : ∀ σx c, Jr σx c → LimOk (ms []) F (σx.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
    (σx.regs.rsp.toBitVec - 8#64 - 8#64 - (80 : Int64).toBitVec)
  hsvc : ∀ F' : MachineData → Prop, FStable (pR (wR R)) F' →
    (∀ m, F' m → ((F m ∧ CallerCells R (-80) (-144) 8 m) ∧ CallerCells (wR R) (-96 - 8) (-40) 16 m) ∧
      Spike.Lib.X64.Rt.WcRa (wR R) ((_root_.Executable.labels exe).label ".Lscc_rt_main.x3") m ∧
      Spike.Lib.X64.Rt.WcFp (wR R) (R.addr (-8)) m) →
    ∀ g' : PG, g'.2.2 = ((_root_.Executable.labels exe).label ".Lwc_main.x15").toBitVec →
    g'.2.1 = (wR R).addr (-8) →
    SegW (fun s c => W s c []) K p lbl (ms [])
      (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .sys))
      (At exe endPc (pR (wR R)) F' (Print.N (_root_.Executable.labels exe).label g'.1 g'.2.1 g'.2.2 .n5))
  hedgeW : ∀ g : AS × Ctl, ∀ σ c, wcJ (wJ0 (_root_.Executable.labels exe).label σC Jr g) σ c →
    σ.regs.get64 .rbp = (wR R).addr (-8) → ∀ σ' : AS,
    (∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σ'.slot k = wcSl (_root_.Executable.labels exe).label σ k) →
    σ'.regs.rax.toBitVec = 0#64 → σ'.regs.rbp.toBitVec = σ.slot (-8) →
    σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 →
    ∃ c', LocalRun p c c' ∧ Jw σ' c'
  hbpw : ∀ σx c, Jw σx c → σx.regs.get64 .rbp = R.addr (-8)
  hok : ∀ s c σx, Jw σx c →
    At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 +
      Int64.ofNat 5, mO, fun _ _ => True⟩ s c → SysOk p (ms []) s c (.exitGroup σx.regs.rax.toNat)

/-- **The source at `rodata`'s allocation**, `scc_rt_main`'s entry `%rsp`
and thread pointer kept (`mainN0`'s ghosts), `%rdi` the thread pointer
(`mainE0`). -/
-- `%rdi` is pinned: the setup frame's `me` must be placed (`PlacedS`), and `%rdi` is where it is.
def rdJ' (g : MainG) (σ : AS) (c : Ctl) : Prop :=
  c = rdCN ∧ σ.regs.rsp.toBitVec = g.sp0 ∧ σ.regs.fsBase = g.tp ∧ σ.regs.rdi.toBitVec = g.tp.toBitVec

/-- **The depth of `scc_rt_main`'s region after a setup block**: its frame
down to `wc_rodata`'s pushed return address (`80`), `wc_rodata`'s and the
allocator's depth below it (`208`, `allocAbortDepth 40`, the heap abort's
node) and the heap abort's dispatcher below the node (`32`: its return
address and the `[-24, 16)` frame). -/
abbrev setupL : Int := 80 + 208 + 32

/-! ## From `scc_rt_main`'s entry -/

section Main

open Spike.Lib.Hello1Src (hello1Src)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` from its entry at the setup block's source**: from
`mainE0` (the source at `setupCall e` in `env`, no frame) the call of
`rodata` and its first steps (`setupCall_run`), cut A at the frame
`setupFrame e env` (`hPre` at `rdJ'`), the allocator's return into cut B
(`hret`, `hPost`). Exits: `print`'s abort with no frame, the heap abort
under the frame. -/
theorem hello1_setup_main_segWS {W : FragS isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    (hK : (ms []).K = some Scc.Sem.X64.abi)
    {e : Expr} {env : TermRun.Env} (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {g : MainG} (hg : g.c0 = ⟨setupCall e, env, none⟩)
    {Jp J1 J2 J3 J4 Jr Jw : MachineData → AS → AS → Ctl → Prop}
    (hWe : ∀ s c, At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g) s c → W s c [])
    (hPre : SetupPreP W K lbl ms exe endPc R F [setupFrame e env] (rdJ' g))
    (hret : ∀ m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl (mR R)
        (mRdJ0 (mNC (_root_.Executable.labels exe).label R (rdJ' g)).J σC) .x13).J σ c →
      Jp m0 σC σ c)
    (hPost : ∀ m0 σC, SetupPostP W K p lbl ms exe endPc R F (setupFrame e env) m0 σC (Jp m0 σC) (J1 m0 σC)
      (J2 m0 σC) (J3 m0 σC) (J4 m0 σC) (Jr m0 σC) (Jw m0 σC)) :
    SegWS W K p lbl ms ((At exe endPc R F (mainE0 (_root_.Executable.labels exe).label g)).at [])
      (fun s c fs => (At exe endPc R F (mAb (_root_.Executable.labels exe).label)).at [] s c fs ∨
        Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
          (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl (mR R)
            (mRdJ0 (mNC (_root_.Executable.labels exe).label R (rdJ' g)).J σC) .abort) s c) [setupFrame e env]
          s c fs) := by
  let lab := (_root_.Executable.labels exe).label
  have hA := hello1_main_pre_segWS (fs1 := [setupFrame e env]) hp hend hF hR hlo hhi
    (J := (mainE0 lab g).J) (J' := rdJ' g)
    (fun σ c ⟨⟨hc, hsp, htp⟩, hx⟩ => ⟨rdCN, hc ▸ hg ▸ setupCall_run hd hu, rfl, hsp, htp, hx⟩) hWe hPre.hW hPre.hlimM
    hPre.hlimR hPre.hq hPre.hmem hPre.hxa
  have hB : SegWS W K p lbl ms
      (fun s c fs => ∃ m0 σC, (At exe endPc (mR R) (mF R F m0 σC)
        (rdX13 lab (Jp m0 σC))).at [setupFrame e env] s c fs)
      ((At exe endPc R F (mAb lab)).at []) :=
    SegWS.exists_pre fun m0 => SegWS.exists_pre fun σC =>
      let h := hPost m0 σC
      hello1_main_post_segWS hp hend hF hR hlo hhi hK rfl h.hW h.hbp h.hra h.hmem h.h1 h.h2 h.h3 h.h4 h.hedge
        h.hbpr h.hlimW h.hsvc h.hedgeW h.hbpw h.hok
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

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}

/-- **`scc_rt_main`'s region after the start** for the new stack's base
`v`: `call scc_rt_main`'s callee region in the new region of depth `L`. -/
abbrev mainR (v : BitVec 64) (L : Int) : Region := (swR v (-L) 0).callee (-8 - 0) (8 - L) 8

/-- **`scc_rt_main`'s frame condition after the start**: the new stack's
(`swFSL`), the caller's cells outside the callee's region holding values. -/
abbrev mainF (rS : Scc.Sem.Range) (tcb top v : BitVec 64) (L : Int) : MachineData → Prop :=
  fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m

/-- **`hello1.w` from the start's entry to `scc_rt_main`'s exits at the
setup block's source**: the start's segment to `MainE` (`hD`), then for
every value `v` of the new stack's base `hello1_setup_main_segWS` in
`scc_rt_main`'s region `mainR v L` under `mainF` (`mainE_ok`: the new
region of depth `L ≥ 296`, `8 ∣ L`, `hL`, `hL8`; no write inside it breaks
the frame condition: `hfit`, `hout`, `hfitS`; `setupL + 8` for the heap
abort's tail). The premises of cuts A and B are asked per `v` (`hPre`,
`hret`, `hPost`). -/
theorem hello1_setup_segWS {W : FragS isa} {K : State → State → Prop} {P0 : FragS isa}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hL : 296 ≤ L) (hL8 : L % 8 = 0) (hK : (ms []).K = some Scc.Sem.X64.abi)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    {e : Expr} {env : TermRun.Env} (hc0 : c0 = ⟨setupCall e, env, none⟩)
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?) (hu : TermRun.evalAt env (.var "u") = some (.unit, []))
    {Jp J1 J2 J3 J4 Jr Jw : BitVec 64 → MachineData → AS → AS → Ctl → Prop}
    (hD : SegWS W K p lbl ms P0 ((MainE exe endPc rS tcb top c0 L).at []))
    (hWe : ∀ s c, MainE exe endPc rS tcb top c0 L s c → W s c [])
    (hPre : ∀ v, SetupPreP W K lbl ms exe endPc (mainR v L) (mainF rS tcb top v L)
      [setupFrame e env] (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩))
    (hret : ∀ v m0 σC σ c,
      (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl (mR (mainR v L))
        (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC)
        .x13).J σ c → Jp v m0 σC σ c)
    (hPost : ∀ v m0 σC, SetupPostP W K p lbl ms exe endPc (mainR v L) (mainF rS tcb top v L) (setupFrame e env)
      m0 σC (Jp v m0 σC) (J1 v m0 σC) (J2 v m0 σC) (J3 v m0 σC) (J4 v m0 σC) (Jr v m0 σC) (Jw v m0 σC)) :
    SegWS W K p lbl ms P0 (fun s c fs => ∃ v : BitVec 64,
      (At exe endPc (mainR v L) (mainF rS tcb top v L) (mAb (_root_.Executable.labels exe).label)).at [] s c fs ∨
      Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR (mainR v L)) (mF (mainR v L) (mainF rS tcb top v L) m0 σC)
        (rX (ms [setupFrame e env]) (_root_.Executable.labels exe).label lbl (mR (mainR v L))
          (mRdJ0 (mNC (_root_.Executable.labels exe).label (mainR v L) (rdJ' ⟨top - 8#64, tpOf tcb, c0⟩)).J σC)
          .abort) s c) [setupFrame e env] s c fs) := by
  refine hD.seq ((SegWS.exists_pre (P := fun v : {v : BitVec 64 // (swR v (-L) 0).OK} =>
      (At exe endPc (mainR v.1 L) (mainF rS tcb top v.1 L)
        (mainE0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩)).at [])
    fun v => (hello1_setup_main_segWS hp hend (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).2
      (mainE_ok (by omega) hL8 v.2 hfit hout hfitS).1
      (show 8 - L ≤ -288 by omega) (show (8 : Int) ≤ 8 by decide) hK hd hu
      (g := ⟨top - 8#64, tpOf tcb, c0⟩) hc0
      (fun s c h => hWe s c ⟨v.1, v.2, h⟩) (hPre v.1) (hret v.1) (hPost v.1)).mono_post
      fun s c fs h => ⟨v.1, h⟩).mono_pre ?_)
  rintro s c fs ⟨⟨v, hok, h⟩, rfl⟩
  exact ⟨⟨v, hok⟩, h, rfl⟩

end Start

end Spike.Lib.X64.Flow.Hello1
