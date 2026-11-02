/-
**hello.w's `hmid` with `scc_rt_thread_init`'s take** (x86-64; the twin of `Spike/Lib/A64HelloHatA.lean`, the
hello counterpart of wake's `Spike/Lib/X64WakeHatA.lean`): from the box's landing past its store to main's clone,
with the callee's segment inside the level and its fence `W ∧ X ∧ NoSetFsAt` under the take of the second stack or
a `clone` refusal (`TakeCK site r1Of Cl`), at the late frame condition `F ∧ StackM r1Of` (the child's stack
private at the clone).

`hello_wc_mid_hatK` from the landing: `WBH`'s nodes (`WcMidWH.antiF₂`, `WcMidWH.noSetFs`) are in `W ∧ X` (`hX`,
wake's `x1W_off`), unmoved by `TakeCK`; `TakeCK` keeps `F` (`takeCK_fK`, from `HMidPAH.fcl`, `fcg`), `R`'s cells
(`takeCKH_kR`, `R.hi ≤ 96`) and the thread pointer (`takeCK_tp`); `TakeCK` is `TakeCKS` at the fence's states
(`hXr`: the site's range is `r1Of` at the take site; wake's `k1W_iff`). The box is published at `.x25`'s `mfence`
(`hpub`); the two pairs to the `spawn` are taken after the segment (`pub_spawnH`, `SegWS.post_run`).

- `HMidPAH`: the named premises at one ghost (wake's `HMidPA`): `wc_main`'s nodes, the reserve's and the second
  TCB's inside `W`, the counters' and the tid word's facts, `R` ending below the second stack and `F` kept by its
  take (`hi96`, `fcl`, `fcg`), the callee at the take (`ti`), `W` and `Wc` at the clone (`wcl`);
- `takeCK_iffH`: `TakeCKS site Cl` is `TakeCK site r1Of Cl` where the site's range is `r1Of` at the site (wake's
  `k1W_iff`);
- `pub_spawnH`: from the published control the two pairs reach `SpawnSrcH` (wake's `pub_spawn`);
- `at_wcNSH_ctl`: the clone's node at any control (wake's `at_wcNS_ctl`);
- `hmid_boxAH`: the segment from `BoxMH` with `r1Of` unmapped (`KeepUn.U`) to `CloneMidH` (wake's `hmid_boxA`).

No absolute address appears in this file.

## Differences from the AArch64 version

- The publication is at `.x25`'s `mfence` (`X64HelloWcPub`), not at a `dmb` past the box's store: `HMidPAH` has
  no source `S` (`wcWf` at `QBH` alone), `hello_wc_mid_hatK` asks `hpub`, `hP`, and exits at the published control
  `boxPubCtlH c0 ty l`; the two pairs to `SpawnSrcH` are a pending frame run (`pub_spawnH`, `SegWS.post_run`), as
  in wake's x86-64 `hmid_boxA`, with `at_wcNSH_ctl` moving the clone's node to the run's control.
- `R`'s end below the second stack is `R.hi ≤ 96` (`hi96`, AArch64 `hi80`), the callees at `-136` (`rARH R`,
  `R.callee (-136) (-184) 8`, `R.callee (-136) (-248) 8`), the callee's region `R.lo ≤ -248`, `8 ≤ R.hi` with
  no alignment premise (AArch64: `-144`, `-256`, `0`, 16-aligned).
- The thread pointer is `fsBase`: `NoMsrAt` is `NoSetFsAt` and the kernel `ms.K = some X64.abi`.
-/
import Spike.Lib.X64HelloHMid

namespace Spike.Lib.X64HelloHatA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.HelloWc (WcMainWH WcMidWH bXH FrMGH rNH ResCtxH TcbCtxH wcNCRH tcb2QH tH rARH wcNIH
  oCH x24L hello_wc_mid_hatK wcMidW_offCH wcMidW_w1H takeCKH_kR stackM_r1H)
open Spike.Lib.X64.HelloPh.WcSp6 (wcNSH MidPGH)
open Spike.Lib.X64.Flow.WakeWc (MidG kOf tiQ pcOf_ne takeCK_fK takeCK_tp)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX CallerCells StackM StOk TakeK)
open Spike.Lib.X64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64ConsumerA (TakeCK TakeCKS)
open Spike.Lib.X64Consumer (Pz)
open Spike.Lib.X64HelloHMid (BoxPureH BoxMH QBH SBH WBH CloneMidH at_bXH_ms)
open Spike.Lib.X64HelloPreA (clonePcH)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH boxPubCtlH)
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Scc.Cert.Rt.X64 (Lays endOf)
open Scc.Sem.X64 (pcOf)

/-- **`hmid`'s named premises at one ghost with the callee's take** (`R`, `F`, `J1`, `tp`) inside the level `W`
and its fence's extra `X` under the memory side `ms` at no frames, for the source `p`, the placement `lbl`, the
box's label `l` at `b` with the slice's words `ws`, the clone's refusal `Cl`; `Wc` the level's extra fact at the
clone: `wc_main`'s nodes, the reserve's and the second TCB's inside `W` (`wcMidW_w1H`'s), the counters' and the tid
word's facts (`hello_wc_mid_hatK`'s), `R` ending below the second stack and `F` kept by its take (`hi96`, `fcl`,
`fcg`: wake's `BoxPure`'s), the callee at the take (`ti`), `W` and `Wc` at the clone (`wcl`). -/
structure HMidPAH (L : RuntimeLayout) (W X : FragS isa) (Wc : Frag isa)
    (ms : List TermRun.Frame → MemSide isa) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (Cl : State → Prop) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (R : Region)
    (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (tp : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W` (`wcMidW_w1H`'s `hwcWf`). -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (QBH l b ws)
  /-- The reserve's nodes inside `W` (`wcMidW_w1H`'s `hres`). -/
  res : ∀ g : Ret0.AllocTcb.G × Ctl, g.1.ra = (L.lab ".Lwc_main.x23").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-136) (-40) 8 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab R J1 (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W` (`wcMidW_w1H`'s `htcb`). -/
  tcb : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab x24L).toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-136) (-184) 8)
      (fun mm => F mm ∧ CallerCells R (-136) (-184) 8 mm ∧
        TcbCtxH L.lab R (wcNCRH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `hello_wc_mid_hatK`'s `hres`. -/
  resA : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `hello_wc_mid_hatK`'s `hhdr`. -/
  hdrA : ∀ c0 g, StOk (ms []) F (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `hello_wc_mid_hatK`'s `htcb`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-136) (-184) 8) F (tcb2QH g c0)
  /-- `hello_wc_mid_hatK`'s `htid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `R` ends below the second stack (wake's `BoxPure`'s bound, at `wc_main`'s base 96 below it:
  `takeCKH_kR`, `stackM_r1H`). -/
  hi96 : R.hi ≤ 96
  /-- `F` closed under the take of `r1Of` (wake's `BoxPure`'s; `takeCK_fK`). -/
  fcl : ∀ m pm, F m → F (Ret0.takeMem pm (r1Of L.lab) m)
  /-- `F` determined by the memory (wake's `BoxPure`'s; `takeCK_fK`). -/
  fcg : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m'
  /-- The callee inside `W ∧ X ∧ NoSetFsAt` at the take of `r1Of` or a refusal (`hello_wc_mid_hatK`'s `hti`;
  wake's `HMidPA.ti`). -/
  ti : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) F' →
      (∀ m, F' m → F m) → R' = R.callee (-136) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -136) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-136) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oCH mC σC ∧ (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-136) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -136) →
            Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => (W s c [] ∧ X s c []) ∧ NoSetFsAt s)
          (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) p lbl (tpXa (ms []) tp)
          (fun s c => At L.exe L.endPc R' F' (tiN L.lab (tiQ (tH L.lab) c0 g) .e) s c ∧ Pz (r1Of L.lab) s.st.1)
          (fun s c => ∃ x, At L.exe L.endPc R' F' (tiX L.lab (tiQ (tH L.lab) c0 g) x) s c ∧
            StackM (r1Of L.lab) s.st.1)
  /-- `W` and its extra `Wc` at the clone's `syscall`, the source at `SpawnSrcH l ws`, the child's stack private
  there (the hat's late frame condition `F ∧ StackM r1Of`; the instance's `Wc := StackM r1Of`). -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c

/-- **`TakeCKS` is the callee's move** where the site's range is `rS` at the take's pc `a` (wake's `k1W_iff`). -/
theorem takeCK_iffH {a : Int64} {rS : Scc.Sem.Range} {Cl : State → Prop} {s : State}
    (hr : s.st.2 = a → Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = rS) (s' : State) :
    TakeCKS a Cl s s' ↔ TakeCK a rS Cl s s' := by
  by_cases ha : s.st.2 = a
  · show TakeK _ (Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s) s s' ∨ _ ↔ TakeK _ _ s s' ∨ _
    rw [hr ha]
  · exact ⟨fun h => h.imp (fun h => (ha h.1).elim) id, fun h => h.imp (fun h => (ha h.1).elim) id⟩

/-- **From the published control to the `spawn`** (wake's `pub_spawn`): with `me` bound to main's id and `sl` to
the slice's words `ws`, the two pairs reach `SpawnSrcH l ws`. -/
theorem pub_spawnH {p : Prog} {c0 : Ctl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word}
    (hme : TermRun.evalAt c0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hsl : TermRun.evalAt c0.env (.var "sl") = some (slTy, ws)) :
    ∃ c', FrameRun p (boxPubCtlH c0 .int l, []) (c', []) ∧ SpawnSrcH l ws c' := by
  have hc : TermRun.evalAt (boxPubCtlH c0 .int l).env (.var "c") =
      some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [boxPubCtlH, TermRun.evalAt, TermRun.lookupE]
  have hs1 : TermRun.evalAt (boxPubCtlH c0 .int l).env (.var "sl") = some (slTy, ws) := by
    simpa [boxPubCtlH, TermRun.evalAt, TermRun.lookupE] using hsl
  have hm1 : TermRun.evalAt (boxPubCtlH c0 .int l).env (.var "me") =
      some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [boxPubCtlH, TermRun.evalAt, TermRun.lookupE] using hme
  have s1 := Spike.Lib.Form.localStep_pair (p := p) (c := boxPubCtlH c0 .int l) rfl hs1 hc
  have hp0 : TermRun.evalAt (("p0", .prod slTy (.ptr .pub .int), ws ++ [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ::
      (boxPubCtlH c0 .int l).env) (.var "p0") =
      some (.prod slTy (.ptr .pub .int), ws ++ [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [TermRun.evalAt, TermRun.lookupE]
  have hm2 : TermRun.evalAt (("p0", .prod slTy (.ptr .pub .int), ws ++ [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ::
      (boxPubCtlH c0 .int l).env) (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [TermRun.evalAt, TermRun.lookupE] using hm1
  have s2 := Spike.Lib.Form.localStep_pair (p := p) (c := ⟨Spike.Lib.X64HelloMainPreSrc.pTerm,
    ("p0", .prod slTy (.ptr .pub .int), ws ++ [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: (boxPubCtlH c0 .int l).env, none⟩)
    rfl hp0 hm2
  refine ⟨_, .step (.loc (LocalStep.toS s1)) (.single (.loc (LocalStep.toS s2))), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [TermRun.evalAt, TermRun.lookupE] using hc
  · simpa [TermRun.evalAt, TermRun.lookupE] using hm1
  · simpa [TermRun.evalAt, TermRun.lookupE] using hs1
  · simp [TermRun.evalAt, TermRun.lookupE]

/-- **The clone's node at any control**: `wcNSH`'s facts pin the control to its parameter. -/
theorem at_wcNSH_ctl {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {lab : Label → Int64} {t k me cA : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c c' : Ctl}
    (h : At exe endPc R F (wcNSH lab c t k sl me cA fr) s c) :
    At exe endPc R F (wcNSH lab c' t k sl me cA fr) s c' := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨⟨-, hJA⟩, hL⟩, hr⟩⟩ := h
  exact ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨⟨rfl, hJA⟩, hL⟩, hr⟩⟩

set_option maxHeartbeats 800000 in
/-- **`hmid` at `l`, `b`, `n` with the callee's take**: from the box's landing `BoxMH` (under `ms0`) with the
second stack unmapped (`U r1Of`) past its store to main's clone (`CloneMidH`) inside the level `W` and the fence's
extra `X`, under the take of the site's range or a refusal `Cl` at the clone (`TakeCKS`), given `ms []`'s kernel
and publication (`hK`, `hpub`), `Cl` at the clone's pc (`hCl`), `X` off both pcs (`hX`; wake's `x1W_off`), the
site's range `r1Of` at the take site in the fence (`hXr`; wake's `X1W`'s take clause), the second stack in the
address space (`hfit1`), the box call's premises and arena geometry from `ms0` (`hokb`, `hg`), and `HMidPAH` at
every ghost of `BoxMH`'s (`hP`). -/
theorem hmid_boxAH {L : RuntimeLayout} {ms0 : MemSide isa} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop} {W X : FragS isa}
    {Wc : Frag isa} {ms : List TermRun.Frame → MemSide isa} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {Cl : State → Prop} {l : WeakMem.AllocLabel} {b n : Nat}
    {ws : List TermRun.Word} (hp : L.prog = SccCode.helloCells) (hK : (ms []).K = some Scc.Sem.X64.abi)
    (hpub : (ms []).pub)
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hX : ∀ s c, pcOf s ≠ clonePcH L → pcOf s ≠ (L.lab Ret0.StackTake.siteL).toBitVec.toNat → X s c [])
    (hXr : ∀ s c, W s c [] → X s c [] → s.st.2 = L.lab Ret0.StackTake.siteL →
      Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = r1Of L.lab)
    (hfit1 : (r1Of L.lab).lo + (r1Of L.lab).size ≤ 2 ^ 64)
    (hokb : ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB ms0 L.lab → q.OKB (ms []) L.lab)
    (hg : (ms []).heap = ms0.heap ∧ (ms []).cells = ms0.cells ∧ (ms []).off = ms0.off ∧
      (ms []).units = ms0.units)
    (hP : ∀ R F J1 t, BoxPureH L F0 n R F J1 t → G R F J1 t → HMidPAH L W X Wc ms p lbl Cl l b ws R F J1 t) :
    SegWS (fun s c fs => W s c fs ∧ X s c fs) (TakeCKS (L.lab Ret0.StackTake.siteL) Cl) p lbl ms
      (fun s c fs => BoxMH L ms0 F0 G l b ws n s c ∧ Spike.Lib.X64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
      (CloneMidH L F0 G W Wc l b ws n) := by
  have hpS : Lays L.exe SccCode.helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloCells L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPureH L F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ G g.1 g.2.1 g.2.2.1 g.2.2.2 ∧
      (At L.exe L.endPc g.1 g.2.1 (bXH ms0 L.lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QBH l b ws l b c ∧
      Spike.Lib.X64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
    fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J1, t⟩ := g
    by_cases hC : BoxPureH L F0 n R F J1 t ∧ G R F J1 t
    case neg =>
      exact ⟨fun _ _ _ => False, fun _ _ _ h => hC ⟨h.1, h.2.1⟩, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨hB, hG⟩ := hC
    have hp' := hP R F J1 t hB hG
    obtain ⟨hR, -, hF, hlo, hhi, hst, -, -, -⟩ := id hB
    have hfence : WcMidWH (NoSetFsW (WBH L W) (fun _ _ => False)) (fun _ _ => False)
        L.exe L.endPc R F (fun m => F m ∧ StackM (r1Of L.lab) m) (tpXa (ms []) t) J1 (QBH l b ws) :=
      Spike.Lib.X64.Flow.HelloWc.WcMidWH.noSetFs hpS hendS
        (Spike.Lib.X64.Flow.HelloWc.WcMidWH.antiF₂ (fun _ h => h.1)
          (Spike.Lib.X64.Flow.HelloWc.WcMidWH.mapWK
            (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk => ⟨⟨hw, pcOf_ne hc, pcOf_ne ha⟩, hk⟩)
            (Spike.Lib.X64.Flow.HelloWc.WcMidWH.and (wcMidW_offCH hpS)
              (wcMidW_w1H W hp'.wcWf hp'.res hp'.tcb))))
    have hW : WcMidWH (fun s c => (W s c [] ∧ X s c []) ∧ NoSetFsAt s)
        (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) L.exe L.endPc R F
        (fun m => F m ∧ StackM (r1Of L.lab) m) (tpXa (ms []) t) J1 (QBH l b ws) :=
      Spike.Lib.X64.Flow.HelloWc.WcMidWH.mapWK (fun s c ⟨⟨hw, hc, ha⟩, hnm, _⟩ _ =>
        ⟨⟨⟨hw, hX s c hc ha⟩, hnm⟩,
          fun s' hk => hk.elim (fun h => ha (by unfold pcOf; rw [h.1])) fun h => hc (hCl s h.1)⟩) hfence
    have hseg := hello_wc_mid_hatK (p := p) (lbl := lbl) (ms := ms []) (t := t)
      (W := fun s c => W s c [] ∧ X s c []) (K := TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl)
      (M := StackM (r1Of L.lab)) (F₂ := fun m => F m ∧ StackM (r1Of L.lab) m)
      hK hpS hendS hF hR hlo hhi
      (fun m m' h hd => ⟨hF m m' h.1 hd, stackM_r1H hp'.hi96 hst hfit1 m m' h.2 hd⟩)
      (fun _ h1 h2 => ⟨h1, h2⟩) hW
      (fun _ _ _ ⟨e1, _, ht, hh, ho, _, _⟩ => ⟨ht, hh, _, by subst e1; exact ho⟩) hpub
      hp'.resA hp'.hdrA hp'.tcbA hp'.tid (takeCK_fK hp'.fcl hp'.fcg)
      (fun s s' hk _ k hk' _ => takeCKH_kR hR hp'.hi96 hst hfit1 s s' hk k hk') takeCK_tp
      (fun s _ _ ⟨ho1, ho2⟩ _ hk => hk.elim (fun h => (ho2 h.1).elim)
        fun h => (pcOf_ne ho1 (hCl s h.1)).elim) hp'.ti
    have hseg := hseg.mono_K (K' := TakeCKS (L.lab Ret0.StackTake.siteL) Cl) fun s c ⟨hw, hx⟩ s' =>
      takeCK_iffH (hXr s c hw hx) s'
    refine SegWS.post_run (((SegWS.liftS [] hseg fun s c h => h).mono_pre ?_).mono_post ?_)
    · rintro s c fs ⟨-, -, ⟨hA, htp⟩, hq, hu, rfl⟩
      exact ⟨⟨⟨l, b, at_bXH_ms hokb hg hA, hq⟩, hu, htp⟩, rfl⟩
    · rintro s c fs ⟨⟨c0, ty, l', sl, me, cA, fr, rfl, ⟨⟨rfl, hcA, -, -, ho', hme, hsl⟩, -, -, ho⟩, hFr, hA, hb,
        htp⟩, rfl⟩
      have hty := congrArg Prod.fst (Option.some.inj (ho.symm.trans ho'))
      cases hty
      obtain ⟨c', hr, hsrc⟩ := pub_spawnH (p := p) (l := l') hme hsl
      have hA' := at_wcNSH_ctl (c' := c') hA
      have hAF : At L.exe L.endPc R F (wcNSH L.lab c' (tH L.lab) (kOf L.lab) sl me cA fr) s c' :=
        let ⟨he, hn', hd, hpc, σ, hAb, hD, hJ'⟩ := hA'; ⟨he, hn', hd, hpc, σ, hAb, hD.1, hJ'⟩
      have hSM : StackM (r1Of L.lab) s.st.1 := let ⟨_, _, _, _, _, _, hD, _⟩ := hA'; hD.2
      have hw := hp'.wcl s c' sl me cA fr hAF hsrc hcA hFr hSM
      exact ⟨c', [], hr, rfl, hw.1, hw.2, R, F, J1, t, sl, me, cA, fr, hB, hG, hFr, hcA, hsrc, hAF, hb, htp⟩
  · rintro s c fs ⟨⟨R, F, J1, t, hB, hG, hAt, hq⟩, hu, rfl⟩
    exact ⟨(R, F, J1, t), hB, hG, hAt, hq, hu, rfl⟩

end Spike.Lib.X64HelloHatA

/-- info: 'Spike.Lib.X64HelloHatA.takeCK_iffH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHatA.takeCK_iffH

/-- info: 'Spike.Lib.X64HelloHatA.pub_spawnH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHatA.pub_spawnH

/-- info: 'Spike.Lib.X64HelloHatA.at_wcNSH_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHatA.at_wcNSH_ctl

/-- info: 'Spike.Lib.X64HelloHatA.hmid_boxAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHatA.hmid_boxAH
