/-
**hello.w's box past its store to main's `clone`, inside a level and its
fence** (AArch64, `HelloHMid`): the
level-generic twin of `Spike/Lib/A64WakeHMid.lean` (wake's `hmid_box`) at
hello's `wc_main` (frame 144).

`hello_wc_mid_hatW` from the box's landing `bXH`, its source facts `QBH`
(the box's, with the slice `sl` bound to the words `ws`), the source at the
clone `SBH` (`SpawnSrcH l ws` at the same `ws`, so the clone keeps the box's
slice: `src_spawnH` at the memory side's
publication `hpub`), its fence off the clone's and the take site's pcs
(`wcMidW_offCH`) and inside the level `W` (`wcMidW_w1H`), at no outside
move; the take of the site's range or a refusal `Cl` at the clone
(`TakeCKS`) moves no state of the fence (`takeCKS_none`, `SegW.mono_K`);
lifted at no frames (`SegWS.liftS`), the fence's extra `X` off both pcs
(`hX`, wake's `x1W_off`).

- `at_bXH_ms`: the landing across memory sides admitting the same box calls
  (wake's `at_bX_ms`).
- `BoxPureH`: the box's facts of its ghosts alone (`R`, `F`, `J1`, `t`, `n`)
  that the hat and `ClonePostH` use (wake's `BoxPure`); the instance's
  other ghost facts are the extra `G`.
- `slWsH`: rodata's slice words (the instance's `ws`).
- `QBH`, `SBH`: the box's source facts and the source at the clone (wake's
  `QB`, `SB`).
- `BoxMH`: the box's landing with its ghosts (the pre; wake's `Box`'s
  shape).
- `WBH`: the level at no frames off the clone's and the take site's pcs
  (wake's `WB`).
- `HMidPH`: the named premises at one ghost (wake's `HMidP`).
- `CloneMidH`: main at the clone's `svc` (wake's `CloneP`);
  `CloneMidH.post`: it is `ClonePostH`.
- `hmid_boxH`: the segment from `BoxMH` to `CloneMidH` (wake's `hmid_box`).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloWcHat
import Spike.Lib.A64HelloWcK1
import Spike.Lib.A64HelloWcW1
import Spike.Lib.A64HelloWcNoMsr
import Spike.Lib.A64HelloWcInv
import Spike.Lib.HelloMainPreSrc

namespace Spike.Lib.HelloHMid

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.HelloWc (WcMainWH bXH FrMGH rNH ResCtxH TcbCtxH wcNCH tcb2QH tH rARH wcNIH
  hello_wc_mid_hatW clonePostH_of wcMidW_offCH wcMidW_w1H)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH wcNSH)
open Spike.Lib.A64.Flow.WakeWc (MidG kOf tiQ pcOf_ne takeCKS_none)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX CallerCells)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.HelloPreA (ClonePostH clonePcH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH src_spawnH boxTermH slTy)
open Spike.Lib.WakeT1 (mainTidLbl)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Sem.A64 (pcOf)

/-- **The landing across memory sides** admitting the same box calls, with
the same arena geometry (`heap`, `cells`, `off`, `units`). -/
theorem at_bXH_ms {ms ms' : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (hq : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms (_root_.Executable.labels exe).label →
      q.OKB ms' (_root_.Executable.labels exe).label)
    (hg : ms'.heap = ms.heap ∧ ms'.cells = ms.cells ∧ ms'.off = ms.off ∧ ms'.units = ms.units)
    (h : At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms' (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := hg
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, hq _ q.2⟩, h1, h2, h3, by rw [g1, g2, g3, g4]; exact h4⟩

/-- **The box's facts of its ghosts alone** that the hat and `ClonePostH`
use: the region `R` (room for `wc_main`'s callees, `R.lo ≤ -400`; its base
80 above stack 0's top less `scc_rt_main`'s frame), the frame condition `F`
(inside `F0`), the thread pointer `t = pinA + 8`, one object. -/
def BoxPureH (L : RuntimeLayout) (F0 : MachineData → Prop) (n : Nat) (R : Region) (F : MachineData → Prop)
    (_J1 : AS → Ctl → Prop) (t : UInt64) : Prop :=
  R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -400 ∧ 0 ≤ R.hi ∧
    R.base.toNat + 80 = L.stacksA.toNat + 16384 ∧ t.toNat = L.pinA.toNat + 8 ∧ n = 1 ∧ ∀ m, F m → F0 m

/-- **rodata's slice words** at its label `l` (`SlRep`'s shape): the buffer
`l`, `m = 2`, `n = 13`; the instance's `ws` at `h2`'s indices. -/
def slWsH (l : WeakMem.AllocLabel) : List TermRun.Word :=
  [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)]

/-- **The box's source facts** at `l` (`b`): `boxTermH`, no hold, `o` at
`l`'s owned locative, `me` at main's, `sl` at the words `ws`. -/
def QBH (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) :
    Prop :=
  l' = l ∧ A = b ∧ c.term = boxTermH ∧ c.hold = none ∧
    TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "sl") = some (slTy, ws)

/-- **The source at the clone** at `l` (`b`): `SpawnSrcH l ws` at the
box's words `ws`. -/
def SBH (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (l' : WeakMem.AllocLabel) (A : Nat) (c : Ctl) :
    Prop :=
  l' = l ∧ A = b ∧ SpawnSrcH l ws c

/-- **The box's landing with its ghosts** at `l`, `b`, `n` under `ms0`:
`BoxPureH` and the instance's extra `G` at the ghosts, `bXH` with the
thread pointer `t`, the source facts `QBH`. -/
def BoxMH (L : RuntimeLayout) (ms0 : MemSide isaLSE2) (F0 : MachineData → Prop)
    (G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (n : Nat) (s : State) (c : Ctl) : Prop :=
  ∃ (R : Region) (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (t : UInt64),
    BoxPureH L F0 n R F J1 t ∧ G R F J1 t ∧
    (At L.exe L.endPc R F (bXH ms0 L.lab J1 l b) s c ∧ TP t s) ∧ QBH l b ws l b c

/-- **The fence the hat runs in**: the level `W` at no frames, off the
clone's pc and the take site's. -/
def WBH (L : RuntimeLayout) (W : FragS isaLSE2) : Frag isaLSE2 := fun s c =>
  W s c [] ∧ pcOf s ≠ clonePcH L ∧ pcOf s ≠ (L.lab Ret0.StackTake.siteL).toBitVec.toNat

/-- **`hmid`'s named premises at one ghost** (`R`, `F`, `J1`, `tp`) inside
the level `W` under the memory side `ms` at no frames, for the source `p`,
the placement `lbl`, the box's label `l` at `b`; `Wc` the level's extra
fact at the clone (wake's `StackM`). -/
structure HMidPH (L : RuntimeLayout) (W : FragS isaLSE2) (Wc : Frag isaLSE2)
    (ms : List TermRun.Frame → MemSide isaLSE2) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (R : Region) (F : MachineData → Prop)
    (J1 : AS → Ctl → Prop) (tp : UInt64) : Prop where
  /-- `wc_main`'s nodes inside `W` (`wcMidW_w1H`'s `hwcWf`; wake's `HMidP.wcWf`). -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (SBH l b ws)
    (QBH l b ws)
  /-- The reserve's nodes inside `W` (`wcMidW_w1H`'s `hres`; wake's `HMidP.res`). -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- The second TCB's nodes inside `W` (`wcMidW_w1H`'s `htcb`; wake's `HMidP.tcb`). -/
  tcb : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `hello_wc_mid_hatW`'s `hres` (wake's `HMidP.resA`). -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `hello_wc_mid_hatW`'s `hhdr` (wake's `HMidP.hdrA`). -/
  hdrA : ∀ c0 g, Ret0.StOk (ms []) F L.exe L.endPc (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `hello_wc_mid_hatW`'s `htcb` (wake's `HMidP.tcbA`). -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0)
  /-- `hello_wc_mid_hatW`'s `htid` (wake's `HMidP.tid`). -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `hello_wc_mid_hatW`'s `hti` inside `WBH`, at no outside move, no post
  beyond the frame (wake's `HMidP.ti`). -/
  ti : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable (fun _ _ => False) F' → (∀ m, F' m → F m) →
      R' = R.callee (-144) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -144) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-144) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oWH mC σC ∧ (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-144) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -144) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (NoMsrW (WBH L W) (fun _ _ => False)) (fun _ _ => False) p lbl (tpXa (ms []) tp)
          (At L.exe L.endPc R' F' (tiN L.lab (tiQ (tH L.lab) c0 g) .e))
          (fun s c => ∃ x, At L.exe L.endPc R' F' (tiX L.lab (tiQ (tH L.lab) c0 g) x) s c ∧ True)
  /-- `W` and its extra `Wc` at the clone's `svc` (wake's `HMidP.wcl`). -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → W s c [] ∧ Wc s c

/-- **main at the clone's `svc`** (`hello_wc_mid_hatW`'s post with the box's
ghosts; wake's `CloneP`): no frames, inside `W` and `Wc`, at `wcNSH` in the
box's region (base `sp + 144`) with `BoxPureH` and `G` at its ghosts, the
caller's saves `FrMGH`, `x13`'s cell `b`, the source at `SpawnSrcH l ws`
(the box's words `ws`), the thread pointer `t`. -/
def CloneMidH (L : RuntimeLayout) (F0 : MachineData → Prop)
    (G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop) (W : FragS isaLSE2)
    (Wc : Frag isaLSE2) (l : WeakMem.AllocLabel) (b : Nat) (ws : List TermRun.Word) (n : Nat) : FragS isaLSE2 :=
  fun s c fs =>
  fs = [] ∧ W s c [] ∧ Wc s c ∧
    ∃ (R : Region) (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (t : UInt64)
      (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64),
      BoxPureH L F0 n R F J1 t ∧ G R F J1 t ∧ FrMGH J1 fr sl me ∧ cA.toNat = b ∧ SpawnSrcH l ws c ∧
      At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c ∧
      (R.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧ TP t s

/-- `t = pinA + 8` as numbers is so as words. -/
theorem pin8_toBitVec {L : RuntimeLayout} {t : UInt64} (ht : t.toNat = L.pinA.toNat + 8) :
    t.toBitVec = L.pinA + 0#64 + 8#64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := t.toBitVec.isLt; have h2 := L.pinA.isLt; have ht' : t.toBitVec.toNat = _ := ht
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **main at the clone's `svc` is `ClonePostH`** (`clonePostH_of`). -/
theorem CloneMidH.post {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop} {W : FragS isaLSE2}
    {Wc : Frag isaLSE2} {l : WeakMem.AllocLabel} {b n : Nat} {ws : List TermRun.Word} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} (h : CloneMidH L F0 G W Wc l b ws n s c fs) : ∃ t, ClonePostH L L.endPc t s c := by
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, ⟨-, hal, -, -, -, htop, ht, -⟩, -, -, -, -, hA, hb, htp⟩ := h
  exact ⟨t, clonePostH_of hal hA hb htp (by omega) (pin8_toBitVec ht)⟩

/-- **`hmid` at `l`, `b`, `n`**: from the box's landing `BoxMH` (under
`ms0`) past its store to main's clone (`CloneMidH`) inside the level `W`
and the fence's extra `X`, under the take of the site's range or a refusal
`Cl` at the clone (`TakeCKS`), given `ms []`'s kernel and publication
(`hK`, `hpub`), `Cl` at the clone's pc (`hCl`), `X` off both pcs (`hX`;
wake's `x1W_off`), the box call's premises and arena geometry from `ms0`
(`hokb`, `hg`; wake's `okb_ms1`, `arW`'s geometry), and `HMidPH` at every
ghost of `BoxMH`'s (`hP`). -/
theorem hmid_boxH {L : RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop} {W X : FragS isaLSE2}
    {Wc : Frag isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {Cl : State → Prop} {l : WeakMem.AllocLabel} {b n : Nat}
    {ws : List TermRun.Word} (hp : L.prog = SccCode.helloProg) (hK : (ms []).K = some Scc.Sem.A64.abi) (hpub : (ms []).pub)
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hX : ∀ s c, pcOf s ≠ clonePcH L → pcOf s ≠ (L.lab Ret0.StackTake.siteL).toBitVec.toNat → X s c [])
    (hokb : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 L.lab → q.OKB (ms []) L.lab)
    (hg : (ms []).heap = ms0.heap ∧ (ms []).cells = ms0.cells ∧ (ms []).off = ms0.off ∧
      (ms []).units = ms0.units)
    (hP : ∀ R F J1 t, BoxPureH L F0 n R F J1 t → G R F J1 t → HMidPH L W Wc ms p lbl l b ws R F J1 t) :
    SegWS (fun s c fs => W s c fs ∧ X s c fs) (TakeCKS (L.lab Ret0.StackTake.siteL) Cl) p lbl ms
      (fun s c fs => BoxMH L ms0 F0 G l b ws n s c ∧ fs = []) (CloneMidH L F0 G W Wc l b ws n) := by
  have hpS : Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloProg L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  refine (SegWS.exists_pre (P := fun (g : Region × (MachineData → Prop) × (AS → Ctl → Prop) × UInt64) s c fs =>
    BoxPureH L F0 n g.1 g.2.1 g.2.2.1 g.2.2.2 ∧ G g.1 g.2.1 g.2.2.1 g.2.2.2 ∧
      (At L.exe L.endPc g.1 g.2.1 (bXH ms0 L.lab g.2.2.1 l b) s c ∧ TP g.2.2.2 s) ∧ QBH l b ws l b c ∧ fs = [])
    fun g => ?_).mono_pre ?_
  · obtain ⟨R, F, J1, t⟩ := g
    by_cases hC : BoxPureH L F0 n R F J1 t ∧ G R F J1 t
    case neg =>
      exact ⟨fun _ _ _ => False, fun _ _ _ h => hC ⟨h.1, h.2.1⟩, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨hB, hG⟩ := hC
    have hp' := hP R F J1 t hB hG
    obtain ⟨hR, hal, hF, hlo, hhi, -, -, -, -⟩ := id hB
    have hfence : Spike.Lib.A64.Flow.HelloWc.WcMidWH (NoMsrW (WBH L W) (fun _ _ => False)) (fun _ _ => False)
        L.exe L.endPc R F F (tpXa (ms []) t) J1 (SBH l b ws) (QBH l b ws) :=
      Spike.Lib.A64.Flow.HelloWc.WcMidWH.noMsr hpS hendS
        (Spike.Lib.A64.Flow.HelloWc.WcMidWH.mapWK
          (fun _ _ ⟨⟨hc, ha⟩, hw⟩ hk => ⟨⟨hw, pcOf_ne hc, pcOf_ne ha⟩, hk⟩)
          (Spike.Lib.A64.Flow.HelloWc.WcMidWH.and (wcMidW_offCH hpS) (wcMidW_w1H W hp'.wcWf hp'.res hp'.tcb)))
    have hseg := hello_wc_mid_hatW (p := p) (lbl := lbl) (ms := ms []) (tp := t) (M := fun _ => True) (F₂ := F)
      hK hpS hendS hF hR hal hlo hhi hF (fun _ h _ => h) hfence
      (fun _ _ _ ⟨e1, e2, ht, hh, ho, hme, hsl⟩ =>
        (src_spawnH hpub ht hh ho hme hsl).imp fun _ h => ⟨h.1, e1, e2, h.2⟩)
      hp'.resA hp'.hdrA hp'.tcbA hp'.tid (KStable.none F) (fun _ _ h => h.elim) hp'.ti
    have hseg := hseg.mono_K (K' := TakeCKS (L.lab Ret0.StackTake.siteL) Cl) fun s _ ⟨_, hc, ha⟩ s' =>
      ⟨fun h => (takeCKS_none hCl (fun e => ha (by unfold pcOf; rw [e])) hc s' h).elim, False.elim⟩
    refine ((SegWS.liftS [] hseg fun s c ⟨hw, hc, ha⟩ => ⟨hw, hX s c hc ha⟩).mono_pre ?_).mono_post ?_
    · rintro s c fs ⟨-, -, ⟨hA, htp⟩, hq, rfl⟩
      exact ⟨⟨⟨l, b, at_bXH_ms hokb hg hA, hq⟩, htp⟩, rfl⟩
    · rintro s c fs ⟨⟨sl, me, cA, fr, ⟨l', A, ⟨e1, e2, hsrc⟩, hcA⟩, hFr, hA, hb, htp⟩, rfl⟩
      subst e1 e2
      have hw := hp'.wcl s c sl me cA fr hA hsrc hcA hFr
      exact ⟨rfl, hw.1, hw.2, R, F, J1, t, sl, me, cA, fr, hB, hG,
        hFr, hcA, hsrc, hA, hb, htp⟩
  · rintro s c fs ⟨⟨R, F, J1, t, hB, hG, hAt, hq⟩, rfl⟩
    exact ⟨(R, F, J1, t), hB, hG, hAt, hq, rfl⟩

end Spike.Lib.HelloHMid

/-- info: 'Spike.Lib.HelloHMid.at_bXH_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHMid.at_bXH_ms

/-- info: 'Spike.Lib.HelloHMid.pin8_toBitVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHMid.pin8_toBitVec

/-- info: 'Spike.Lib.HelloHMid.CloneMidH.post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHMid.CloneMidH.post

/-- info: 'Spike.Lib.HelloHMid.hmid_boxH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHMid.hmid_boxH
