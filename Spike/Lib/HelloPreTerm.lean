/-
**hello.w: main's source thread before the spawn, step by step** (B8,
`helloSrc_frzL`'s term half; hello's `SpawnViewLtSteps.MainPre` twin, and
the term tracking for hello's `VPre`).

From the start (`WakeT1.setupStartT 2`) to `main`'s `spawn`, main's source
thread runs a fixed sequence of 23 controls (`hc k`): the setup block's call
of `rodata` (frame `frS`), `rodata`'s body (`HelloRodataSrc`'s controls:
the buffer's `newBuf` at label `lbB`, the two lane exchanges, the
publication, the slice), the return into the setup's continuation, the
tail call of `main` and `main`'s body (`HelloMainPreSrc`'s controls: the
`split`, `z`, the box's `new` at label `lbX`, its publication, the packet)
up to `spawnTermH`. Only the two exchange words `wo0`, `wo1` are unknown.

- `lbB`, `lbX`: the buffer's and the box's labels (`freshLabel 0 2 0 1`,
  `freshLabel 0 2 0 2`); `meW`, `envSU`, `frS`, `slW`: main's id word, the
  start's environment, the setup call's frame, the slice's words.
- `hc k wo0 wo1`, `hfs k`, `hna k`: stage `k`'s control, frames and
  allocation count; `HAt th k wo0 wo1`: thread `th` at stage `k`.
- `NewBufE`, `LaneE i`, `BoxE`, `Eff k`: what a step at stage `k` does to the
  memory, the promises and coherence; `FlagMem`: the box's word as a flag
  cell after its `new` (`alloc_flagMem`).
- `hat_tstep`: a thread step from stage `k` lands at stage `k + 1` with
  effect `Eff k` (none from the `spawn`, stage 22).
-/
import Spike.Lib.HelloMainPreSrc
import Spike.Lib.HelloRodataSrc
import Spike.Lib.SrcCalls

namespace Spike.Lib.HelloPreTerm

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalStepS localStepS_atom localStepS_nameI localStepS_asLanes localStepS_pair)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2 τ8 env0 envN bBind envA env1 env2 env3 env4 bufElem_b)
open Spike.Lib.HelloRodataSrc
open Spike.Lib.HelloMainPreSrc

/-! ## The stages -/

/-- The buffer's label: main's first allocation (`freshLabel 0 2 0 1`). -/
abbrev lbB : WeakMem.AllocLabel := 2

/-- The box's label: main's second allocation (`freshLabel 0 2 0 2`). -/
abbrev lbX : WeakMem.AllocLabel := 4

theorem lbB_eq : freshLabel 0 2 0 1 = lbB := rfl
theorem lbX_eq : freshLabel 0 2 0 2 = lbX := rfl

/-- main's `ThreadId` word. -/
def meW : Word := cst (.loc ⟨mainTidLbl 2, 0⟩ 0)

/-- The start's environment. -/
def envSU : Env := [("me", .tid, [meW]), ("u", .unit, [])]

/-- The setup call's frame: return into `r`, then `SrcCalls.setupCont`. -/
def frS : Frame := ⟨"r", SrcCalls.setupCont, envSU, [], slTy⟩

/-- The slice's words: the buffer's locative, `2`, `13`. -/
def slW : List Word := [cst (.loc ⟨lbB, 0⟩ 0), cst (.num 2), cst (.num 13)]

/-- The environment past `r`. -/
def envR' : Env := ("r", slTy, slW) :: envSU

/-- The environment past the box's `new`. -/
def envO : Env := ("o", .ptr .own .int, [cst (.loc ⟨lbX, 0⟩ 0)]) ::
  (c0H (cst (.loc ⟨lbB, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) meW).env

/-- The environment past the box's publication. -/
def envC : Env := ("c", .ptr .pub .int, [cst (.loc ⟨lbX, 0⟩ 0)]) :: envO

/-- The environment past `p0`. -/
def envP0 : Env := ("p0", .prod slTy (.ptr .pub .int), slW ++ [cst (.loc ⟨lbX, 0⟩ 0)]) :: envC

/-- **Stage `k`'s control** (exchange words `wo0`, `wo1`). -/
def hc (k : Nat) (wo0 wo1 : Word) : Ctl :=
  match k with
  | 0 => ⟨Scc.Sem.SrcSem.setupTerm, envSU, none⟩
  | 1 => rdC0
  | 2 => ⟨eM, ("two", .intS (.lit 2), [cst (.num 2)]) :: env0, none⟩
  | 3 => rdCN
  | 4 => rdCA lbB 2
  | 5 => rdC1 lbB 2
  | 6 => rdC2 lbB 2 wo0
  | 7 => rdC3 lbB 2 wo0
  | 8 => rdC4 lbB 2 wo0 wo1
  | 9 => rdC5 lbB 2 wo0 wo1
  | 10 => ⟨eSm, ("n", .intS (.lit 13), [cst (.num 13)]) :: env5 lbB 2 wo0 wo1, none⟩
  | 11 => ⟨eSl0, (envR lbB 2 wo0 wo1).drop 2, none⟩
  | 12 => ⟨ePack, (envR lbB 2 wo0 wo1).drop 1, none⟩
  | 13 => rdRet lbB 2 wo0 wo1
  | 14 => ⟨SrcCalls.setupCont, envR', none⟩
  | 15 => ⟨.tail "main" [] (.var "a"), ("a", .prod slTy .tid, slW ++ [meW]) :: envR', none⟩
  | 16 => mainC (cst (.loc ⟨lbB, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) meW
  | 17 => ⟨zTerm, envS (cst (.loc ⟨lbB, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) meW, none⟩
  | 18 => c0H (cst (.loc ⟨lbB, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) meW
  | 19 => ⟨boxTermH, envO, none⟩
  | 20 => ⟨p0Term, envC, none⟩
  | 21 => ⟨pTerm, envP0, none⟩
  | _ => ⟨spawnTermH, ("p", pktTy, slW ++ [cst (.loc ⟨lbX, 0⟩ 0), meW]) :: envP0, none⟩

/-- Stage `k`'s frames: the setup call's inside `rodata`. -/
def hfs (k : Nat) : List Frame := if 1 ≤ k ∧ k ≤ 13 then [frS] else []

/-- Stage `k`'s allocation count. -/
def hna (k : Nat) : Nat := if k ≤ 3 then 1 else if k ≤ 18 then 2 else 3

/-- **main's thread at stage `k`.** -/
def HAt (th : TTh) (k : Nat) (wo0 wo1 : Word) : Prop :=
  k ≤ 22 ∧ th.term = (hc k wo0 wo1).term ∧ th.env = (hc k wo0 wo1).env ∧ th.σs = [] ∧ th.stack = hfs k ∧
    th.nalloc = hna k

/-- The start is stage 0. -/
theorem hat_start : HAt ((Spike.Lib.WakeT1.setupStartT 2).ths[0]'(by decide)) 0 meW meW :=
  ⟨by decide, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The effects -/

/-- The lane words rodata stores (`HelloPreA.bufW`). -/
def bufV (i : Nat) : Nat := if i = 0 then rdK1 else rdK2

/-- **`newBuf`'s effect**: two messages to the buffer's words pushed,
coherence there at them; the promises kept. -/
def NewBufE (mem : WeakMem.Memory) (th : TTh) (mem' : WeakMem.Memory) (th' : TTh) : Prop :=
  mem'.size = mem.size + 2 ∧ (∀ k < mem.size, mem'[k]? = mem[k]?) ∧
    (∀ i < 2, ∃ m, mem'[mem.size + i]? = some m ∧ m.loc = ⟨lbB, i⟩) ∧
    (∀ i < 2, th'.vs.coh ⟨lbB, i⟩ = mem.size + i) ∧ th'.promises = th.promises

/-- **A lane exchange's effect at word `i`**: the store of `bufV i` appends
or fulfils a promise above coherence there; coherence elsewhere only grows. -/
def LaneE (i : Nat) (mem : WeakMem.Memory) (th : TTh) (mem' : WeakMem.Memory) (th' : TTh) : Prop :=
  (∃ t, ((∃ v, mem' = mem.push ⟨⟨lbB, i⟩, .num (bufV i), v⟩) ∧ t = mem.size ∧ th'.promises = th.promises ∨
      mem' = mem ∧ t ∈ th.promises ∧ th'.promises = th.promises.erase t ∧ th.vs.coh ⟨lbB, i⟩ < t ∧
        ∃ m, mem[t]? = some m ∧ m.loc = ⟨lbB, i⟩ ∧ m.val = .num (bufV i))) ∧
    ∀ b, b ≠ ⟨lbB, i⟩ → th.vs.coh b ≤ th'.vs.coh b

/-- **The flag cell at label `l`** (`SpawnFlag.FlagMem`'s twin): an earlier
message at `⟨l, 0⟩`, then a message there holding `0`, after which every
message there is among the promises `P`. -/
def FlagMem (mem : WeakMem.Memory) (P : List WeakMem.Ts) (l : WeakMem.AllocLabel) : Prop :=
  ∃ i j, i < j ∧ (∃ m, mem[i]? = some m ∧ m.loc = ⟨l, 0⟩) ∧
    (∃ m, mem[j]? = some m ∧ m.loc = ⟨l, 0⟩ ∧ m.val = .num 0) ∧
    ∀ (k : Nat) m, j < k → mem[k]? = some m → m.loc = ⟨l, 0⟩ → k ∈ P

/-- **The box's `new`**: memory grows by messages to the box's label (a
prefix kept); a promise it discharges is a message to the box's label; the
box's word is a flag cell (`FlagMem`). -/
def BoxE (mem : WeakMem.Memory) (th : TTh) (mem' : WeakMem.Memory) (th' : TTh) : Prop :=
  mem.size < mem'.size ∧ (∀ k < mem.size, mem'[k]? = mem[k]?) ∧
    (∀ k m, mem.size ≤ k → mem'[k]? = some m → m.loc.label = lbX) ∧
    (∀ t ∈ th.promises, t ∈ th'.promises ∨ ∃ m, mem'[t]? = some m ∧ m.loc.label = lbX) ∧
    FlagMem mem' th'.promises lbX

/-- **The effect of a step at stage `k`**: the buffer's `newBuf` (3), the
lane exchanges (5, 7), the box's `new` (18); any other step keeps memory,
promises and coherence. -/
def Eff (k : Nat) (mem : WeakMem.Memory) (th : TTh) (mem' : WeakMem.Memory) (th' : TTh) : Prop :=
  match k with
  | 3 => NewBufE mem th mem' th'
  | 5 => LaneE 0 mem th mem' th'
  | 7 => LaneE 1 mem th mem' th'
  | 18 => BoxE mem th mem' th'
  | _ => mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh

/-! ## The steps -/

section Steps

variable {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List WeakMem.Ts} {th th' : TTh} {wo0 wo1 : Word}

theorem close_nil (t : Ty) : close [] t = t := TermStep.substTs_nil' t 0 0

/-- **A local step** from stage `k` to `k + 1`. -/
theorem hat_local {k : Nat} (hk : k + 1 ≤ 22) (hl : LocalStepS helloSrc (hc k wo0 wo1) (hc (k + 1) wo0 wo1))
    (hf : hfs (k + 1) = hfs k) (hn : hna (k + 1) = hna k) (hg : g.p = helloSrc) (h : HAt th k wo0 wo1)
    (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    HAt th' (k + 1) wo0 wo1 ∧ mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [hl.2 g mem pairs th hg ht he hσ, List.mem_singleton] at hr
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, -, rfl⟩ := hr
  exact ⟨⟨hk, rfl, rfl, hσ, hs.trans hf.symm, hna.trans hn.symm⟩, rfl, rfl, rfl⟩

/-- `let x = pack a` at any depth (`Form.localStep_pack`). -/
theorem localStepS_pack {c : Ctl} {x : String} {e : Expr} {a : At} {w : String} {τ : Ty} {t : Ty} {ws : List Word}
    (ht : c.term = .let_ x (.pack a w τ) e) (ha : evalAt c.env a = some (t, ws)) :
    LocalStepS helloSrc c ⟨e, (x, close [] τ, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he hσ
  simp [tstep, ht', ht, evalOp, he, ha, hσ, ol, withS, stOf]

/-- A source load raises no coherence view (`WakeM0.stepLoad_coh_mono`). -/
theorem stepLoad_coh {arch : WeakMem.Arch} {pairs : List Nat} {t t' : Promises.Thread} {dst : WeakMem.Reg}
    {a : WeakMem.Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : t' ∈ Promises.stepLoad arch mem pairs t dst a deps acq) (b : WeakMem.Address) :
    t.vs.coh b ≤ t'.vs.coh b := by
  unfold Promises.stepLoad at h
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp h
  simp only
  split
  · rename_i hb; subst hb; exact Nat.le_max_left _ _
  · exact Nat.le_refl _


/-- The local steps between the stages. -/
theorem hc_local (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 14 ∨
    k = 16 ∨ k = 17 ∨ k = 20 ∨ k = 21) : LocalStepS helloSrc (hc k wo0 wo1) (hc (k + 1) wo0 wo1) := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact localStepS_atom (c := rdC0) rfl rfl
  · exact localStepS_nameI (c := hc 2 wo0 wo1) rfl rfl
  · exact localStepS_asLanes (c := hc 4 wo0 wo1) (n := rdK1) rfl rfl rfl
  · exact localStepS_asLanes (c := hc 6 wo0 wo1) (n := rdK2) rfl rfl rfl
  · exact localStepS_atom (c := hc 9 wo0 wo1) rfl rfl
  · exact localStepS_pair (c := hc 10 wo0 wo1) rfl rfl rfl
  · exact localStepS_pair (c := hc 11 wo0 wo1) rfl rfl rfl
  · exact localStepS_pack (c := hc 12 wo0 wo1) rfl rfl
  · exact localStepS_pair (c := hc 14 wo0 wo1) rfl rfl rfl
  · exact step_split _ _ _ _
  · exact step_z _ _ _ _
  · exact localStepS_pair (c := hc 20 wo0 wo1) rfl rfl rfl
  · exact localStepS_pair (c := hc 21 wo0 wo1) (ws := slW ++ [cst (.loc ⟨lbX, 0⟩ 0)]) (us := [meW]) rfl rfl rfl

theorem rd_decl : ∃ d, helloSrc[2]? = some d ∧ d.body = rdBody ∧ d.arg = "u" ∧ d.argTy = .unit ∧
    close [] d.retTy = slTy := ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem rodata_find : helloSrc.find? (·.name == "rodata") = helloSrc[2]? := rfl

theorem main_findH : helloSrc.find? (·.name == "main") = some mainD := rfl

theorem zeroable8 : zeroableIn [] [] (close [] τ8) = true := by rw [close_nil]; simp [zeroableIn]

theorem zeroWords8 : zeroWords (close [] τ8) = some [.num 0] := by rw [close_nil]; simp [zeroWords]

/-- **The setup's call of `rodata`** (stage 0 to 1): the frame `frS`
pushed, `rodata`'s body entered on `u`. -/
theorem hat_call (hg : g.p = helloSrc) (h : HAt th 0 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    HAt th' 1 wo0 wo1 ∧ mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  simp only [hc] at ht he
  simp only [hfs] at hs
  obtain ⟨d, hd, hb, ha, hat, hrt⟩ := rd_decl
  simp [tstep, ht, Scc.Sem.SrcSem.setupTerm, callFrame, enter, hg, rodata_find, he, hσ, hs, hd, hb, ha, hat, hrt,
    envSU, evalAt, lookupE, ol] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact ⟨⟨by decide, rfl, rfl, rfl, rfl, hna⟩, rfl, rfl, rfl⟩

/-- **The buffer's `newBuf`** (stage 3 to 4) at label `lbB`. -/
theorem hat_newBuf (hb : g.lbase = 0) (hn : g.n = 2) (hi : g.i = 0) (h : HAt th 3 wo0 wo1)
    (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : HAt th' 4 wo0 wo1 ∧ NewBufE mem th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  have ha : accs (close [] τ8) = some [.one] := rfl
  simp [evalOp, he, hσ, hc, rdCN, envN, evalAt, lookupE, numOf, ol, allocBuf, zeroable8, zeroWords8, ha, lbB_eq,
    hb, hn, hi, stOf, hna, Spike.Lib.HelloPreTerm.hna] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hn1 : nWords [Acc.one] = 1 := rfl
  refine ⟨⟨by decide, rfl, rfl, rfl, hs, rfl⟩, by simp [hn1], fun k hk => by simp [Array.getElem?_append_left hk],
    fun i hi => ?_, fun i hi => ?_, rfl⟩
  · match i, hi with
    | 0, _ => simp [hn1, offs]
    | 1, _ => simp [hn1, offs]
  · match i, hi with
    | 0, _ => simp [withS, hn1]
    | 1, _ => simp [withS, hn1]

/-- **The first lane exchange** (stage 5 to 6): the store of `rdK1` at the
buffer's word 0, binding the old word `wo0'`. -/
theorem hat_xchg0 (h : HAt th 5 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    ∃ wo0', HAt th' 6 wo0' wo1 ∧ LaneE 0 mem th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  have ha : accs τ8 = some [.one] := rfl
  simp [evalOp, he, hc, rdC1, env1, envA, bBind, evalAt, lookupE, numOf, addrOf, ha, bufElem_b] at hr
  obtain ⟨s2, t, ws, hm, rfl, rfl, rfl⟩ := hr
  simp [loadUnits, storeUnits, offs, dataE, cst] at hm
  obtain ⟨s1, b, ⟨t1, hl, rfl, rfl⟩, s2', ⟨mem2, t2, hst, rfl⟩, rfl, rfl, rfl⟩ := hm
  have hc1 := stepLoad_coh hl
  obtain ⟨t, hcase, hcoh, -, -⟩ := TermStep.stepStore_casesC hst
  refine ⟨t1.regs 1, ⟨by decide, rfl, rfl, by simp [withS, hσ], by simp [withS, hs, hfs],
    by simp [withS, stOf, hna, Spike.Lib.HelloPreTerm.hna]⟩, ⟨t, ?_⟩, fun b hb => ?_⟩
  · rcases hcase with ⟨rfl, rfl, hp⟩ | ⟨rfl, hp, hp', hlt, m, hm, hml, hmv, -⟩
    · exact .inl ⟨⟨_, rfl⟩, rfl, by simp [withS, hp, mth, stOf]⟩
    · exact .inr ⟨by simp, by simpa [mth, stOf] using hp, by simpa [withS, mth, stOf] using hp',
        Nat.lt_of_le_of_lt (hc1 _) hlt, m, by simpa [stOf] using hm, hml, by rw [hmv]; rfl⟩
  · have := hc1 b
    simp only [withS, hcoh, ite_eq_right hb]
    simpa [mth, stOf] using this

/-- **The second lane exchange** (stage 7 to 8): the store of `rdK2` at the
buffer's word 1, binding the old word `wo1'`. -/
theorem hat_xchg1 (h : HAt th 7 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    ∃ wo1', HAt th' 8 wo0 wo1' ∧ LaneE 1 mem th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  have ha : accs τ8 = some [.one] := rfl
  simp [evalOp, he, hc, rdC3, env3, env2, env1, envA, bBind, evalAt, lookupE, numOf, addrOf, ha, bufElem_b] at hr
  obtain ⟨s2, t, ws, hm, rfl, rfl, rfl⟩ := hr
  simp [loadUnits, storeUnits, offs, dataE, cst] at hm
  obtain ⟨s1, b, ⟨t1, hl, rfl, rfl⟩, s2', ⟨mem2, t2, hst, rfl⟩, rfl, rfl, rfl⟩ := hm
  have hc1 := stepLoad_coh hl
  obtain ⟨t, hcase, hcoh, -, -⟩ := TermStep.stepStore_casesC hst
  refine ⟨t1.regs 1, ⟨by decide, rfl, rfl, by simp [withS, hσ], by simp [withS, hs, hfs],
    by simp [withS, stOf, hna, Spike.Lib.HelloPreTerm.hna]⟩, ⟨t, ?_⟩, fun b hb => ?_⟩
  · rcases hcase with ⟨rfl, rfl, hp⟩ | ⟨rfl, hp, hp', hlt, m, hm, hml, hmv, -⟩
    · exact .inl ⟨⟨_, rfl⟩, rfl, by simp [withS, hp, mth, stOf]⟩
    · exact .inr ⟨by simp, by simpa [mth, stOf] using hp, by simpa [withS, mth, stOf] using hp',
        Nat.lt_of_le_of_lt (hc1 _) hlt, m, by simpa [stOf] using hm, hml, by rw [hmv]; rfl⟩
  · have := hc1 b
    have hb' : b ≠ ⟨lbB, nWords [Acc.one]⟩ := hb
    simp only [withS, hcoh, ite_eq_right hb']
    simpa [mth, stOf] using this

/-- **rodata's publication** (stage 8 to 9): a store fence. -/
theorem hat_pubB (h : HAt th 8 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    HAt th' 9 wo0 wo1 ∧ mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  simp [evalOp, he, ol, hc, rdC4, env4, env3, env2, env1, envA, bBind, evalAt, lookupE] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact ⟨⟨by decide, rfl, rfl, hσ, hs, hna⟩, rfl, rfl, rfl⟩

/-- **rodata's return** (stage 13 to 14) into the setup's continuation. -/
theorem hat_ret (h : HAt th 13 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    HAt th' 14 wo0 wo1 ∧ mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  simp only [hc, rdRet, eRet] at ht
  simp [tstep, ht, hs, hfs, he, hc, rdRet, envR, evalAt, lookupE] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact ⟨⟨by decide, rfl, rfl, rfl, rfl, hna⟩, rfl, rfl, rfl⟩

/-- **The tail call of `main`** (stage 15 to 16). -/
theorem hat_tail (hg : g.p = helloSrc) (h : HAt th 15 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    HAt th' 16 wo0 wo1 ∧ mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  simp only [hc] at ht
  simp [tstep, ht, enter, hg, main_findH, he, hc, evalAt, lookupE, ol] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact ⟨⟨by decide, rfl, rfl, rfl, by simp [hs, hfs], hna⟩, rfl, rfl, rfl⟩

/-- **A one-word `new` at the box's label**: memory grows by messages to
it, a prefix kept, a discharged promise a message to it, one more
allocation, the box's locative. -/
theorem alloc_boxE {k : Promises.Knobs} {arch : WeakMem.Arch} {ws : List Word} {s s' : St} {pw : Word}
    (h : (s', pw) ∈ alloc k arch lbX [.one] ws s) :
    s.mem.size < s'.mem.size ∧ (∀ j < s.mem.size, s'.mem[j]? = s.mem[j]?) ∧
      (∀ j m, s.mem.size ≤ j → s'.mem[j]? = some m → m.loc.label = lbX) ∧
      (∀ t ∈ s.promises, t ∈ s'.promises ∨ ∃ m, s'.mem[t]? = some m ∧ m.loc.label = lbX) ∧
      s'.nalloc = s.nalloc + 1 ∧ pw = cst (.loc ⟨lbX, 0⟩ 0) := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  cases ws with
  | nil => simp [storeUnits] at hs2
  | cons w ws =>
    simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at hs2
    obtain ⟨⟨mem', th⟩, hst, rfl⟩ := hs2
    obtain ⟨t, hc, -⟩ := TermStep.stepStore_casesC hst
    have hn : nWords [Acc.one] = 1 := rfl
    simp only [hn, List.range_one, List.foldl_cons, List.foldl_nil, mth, offs] at hc ⊢
    refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
    · rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩ <;> simp <;> omega
    · intro j hj
      rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
      · rw [TermMem.push_lt (by simp; omega), TermMem.push_lt hj]
      · rw [TermMem.push_lt hj]
    · intro j m hj hm
      rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
      · rw [Array.getElem?_push] at hm
        split at hm
        · cases hm; rfl
        · rw [Array.getElem?_push] at hm
          split at hm
          · cases hm; rfl
          · have := TermLiveProps.lt_of_get hm; simp at *; omega
      · rw [Array.getElem?_push] at hm
        split at hm
        · cases hm; rfl
        · have := TermLiveProps.lt_of_get hm; simp at *; omega
    · intro t' ht'
      rcases hc with ⟨rfl, -, hp⟩ | ⟨rfl, -, hp, -, m, hm, hml, -⟩
      · exact .inl (by simpa [hp] using ht')
      · by_cases he : t' = t
        · subst he
          exact .inr ⟨m, hm, by rw [hml]⟩
        · exact .inl (by rw [hp]; exact (List.mem_erase_of_ne he).2 ht')

/-- **`new` of the word `0`** (`SpawnFlag.alloc_flag`'s twin): its store
appends after the `undef` message (a fulfilled promise would lie above the
raised coherence, the top of the memory), so its label has `FlagMem`. -/
theorem alloc_flagMem {k : Promises.Knobs} {arch : WeakMem.Arch} {lbl : WeakMem.AllocLabel} {s s' : St}
    {pw : Word} (h : (s', pw) ∈ alloc k arch lbl [.one] [cst (.num 0)] s) : FlagMem s'.mem s'.promises lbl := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  simp only [storeUnits, List.mem_flatMap, List.mem_singleton] at hs2
  obtain ⟨⟨mem', th⟩, hst, rfl⟩ := hs2
  have hr : List.range (nWords [Acc.one]) = [0] := rfl
  simp only [hr, List.foldl] at hst
  obtain ⟨t, hc, -, -, -⟩ := TermStep.stepStore_casesC hst
  rcases hc with ⟨rfl, -, hp⟩ | ⟨rfl, -, -, hlt, m, hm, -⟩
  · have h1 : ∀ (a : WeakMem.Memory) (x y : WeakMem.Msg), ((a.push x).push y)[a.size]? = some x := by
      intro a x y; rw [TermMem.push_lt (by simp), Array.getElem?_push_size]
    have h2 : ∀ (a : WeakMem.Memory) (x y : WeakMem.Msg), ((a.push x).push y)[a.size + 1]? = some y := by
      intro a x y; rw [← Array.size_push (xs := a) (v := x), Array.getElem?_push_size]
    refine ⟨s.mem.size, s.mem.size + 1, Nat.lt_succ_self _, ⟨_, h1 _ _ _, rfl⟩, ⟨_, h2 _ _ _, rfl, ?_⟩, ?_⟩
    · simp [TermMem.exprVal, dataE, cst, Promises.TVal.mk0]
    · intro k m hk hm
      have := TermLiveProps.lt_of_get hm
      simp only [Array.size_push] at this
      omega
  · exfalso
    have := TermLiveProps.lt_of_get hm
    simp only [mth, offs, nWords, Array.size_push] at hlt this
    simp only [List.map, List.sum_cons, List.sum_nil, Acc.size] at hlt
    simp at hlt
    simp only [WeakMem.Ts] at *
    omega

/-- **The box's `new`** (stage 18 to 19) at label `lbX`. -/
theorem hat_new (hb : g.lbase = 0) (hn : g.n = 2) (hi : g.i = 0) (h : HAt th 18 wo0 wo1)
    (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : HAt th' 19 wo0 wo1 ∧ BoxE mem th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  obtain ⟨_, _, _, hr, tys, hr'⟩ := TermRun.tstep_new_mem ht hr
  have hl : freshLabel g.lbase g.n g.i th.nalloc = lbX := by rw [hb, hn, hi, hna]; rfl
  simp only [evalOp, he, hc, c0H, evalAt, lookupE, List.find?] at hr
  have hacc : accs .int = some [.one] := rfl
  simp only [show ("z" == "z") = true from rfl, Option.map_some, hacc, List.map_map, List.mem_map,
    Function.comp_def] at hr
  obtain ⟨⟨s2, pw⟩, ha, he2⟩ := hr
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  simp only [Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl, rfl⟩ := hr'
  have ha' : (s2, pw) ∈ alloc g.k g.arch lbX [.one] [cst (.num 0)] (stOf mem pairs th) := by
    rw [← hl]; exact ha
  have hf := alloc_flagMem ha'
  obtain ⟨h1, h2, h3, h4, h5, rfl⟩ := alloc_boxE ha'
  refine ⟨⟨by decide, rfl, by simp only [withS, he]; rfl, by simp [withS, hσ], by simp [withS, hs, hfs], ?_⟩,
    h1, h2, h3, h4, ?_⟩
  · simp [withS, h5, hna, Spike.Lib.HelloPreTerm.hna, stOf]
  · simpa [withS] using hf

/-- **The box's publication** (stage 19 to 20): a store fence. -/
theorem hat_pubX (h : HAt th 19 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    HAt th' 20 wo0 wo1 ∧ mem' = mem ∧ th'.promises = th.promises ∧ th'.vs.coh = th.vs.coh := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  simp [evalOp, he, ol, hc, envO, evalAt, lookupE] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact ⟨⟨by decide, rfl, rfl, hσ, hs, hna⟩, rfl, rfl, rfl⟩

/-- **The `spawn` is no thread step** (stage 22). -/
theorem hat_spawn (h : HAt th 22 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : False := by
  obtain ⟨-, ht, -⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  simp [evalOp] at hr

/-- **A thread step from stage `k`** lands at stage `k + 1`, with effect
`Eff k` (at main's `G`: `helloSrc`, label base 0, stripe 2, thread 0). -/
theorem hat_tstep {k : Nat} (hg : g.p = helloSrc) (hb : g.lbase = 0) (hn : g.n = 2) (hi : g.i = 0)
    (h : HAt th k wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    ∃ wo0' wo1', HAt th' (k + 1) wo0' wo1' ∧ Eff k mem th mem' th' := by
  match k, h.1 with
  | 0, _ => exact ⟨_, _, hat_call hg h hr⟩
  | 1, _ => exact ⟨_, _, hat_local (by decide) (hc_local 1 (by decide)) rfl rfl hg h hr⟩
  | 2, _ => exact ⟨_, _, hat_local (by decide) (hc_local 2 (by decide)) rfl rfl hg h hr⟩
  | 3, _ => exact ⟨_, _, hat_newBuf hb hn hi h hr⟩
  | 4, _ => exact ⟨_, _, hat_local (by decide) (hc_local 4 (by decide)) rfl rfl hg h hr⟩
  | 5, _ => obtain ⟨w, h', he⟩ := hat_xchg0 h hr; exact ⟨w, _, h', he⟩
  | 6, _ => exact ⟨_, _, hat_local (by decide) (hc_local 6 (by decide)) rfl rfl hg h hr⟩
  | 7, _ => obtain ⟨w, h', he⟩ := hat_xchg1 h hr; exact ⟨_, w, h', he⟩
  | 8, _ => exact ⟨_, _, hat_pubB h hr⟩
  | 9, _ => exact ⟨_, _, hat_local (by decide) (hc_local 9 (by decide)) rfl rfl hg h hr⟩
  | 10, _ => exact ⟨_, _, hat_local (by decide) (hc_local 10 (by decide)) rfl rfl hg h hr⟩
  | 11, _ => exact ⟨_, _, hat_local (by decide) (hc_local 11 (by decide)) rfl rfl hg h hr⟩
  | 12, _ => exact ⟨_, _, hat_local (by decide) (hc_local 12 (by decide)) rfl rfl hg h hr⟩
  | 13, _ => exact ⟨_, _, hat_ret h hr⟩
  | 14, _ => exact ⟨_, _, hat_local (by decide) (hc_local 14 (by decide)) rfl rfl hg h hr⟩
  | 15, _ => exact ⟨_, _, hat_tail hg h hr⟩
  | 16, _ => exact ⟨_, _, hat_local (by decide) (hc_local 16 (by decide)) rfl rfl hg h hr⟩
  | 17, _ => exact ⟨_, _, hat_local (by decide) (hc_local 17 (by decide)) rfl rfl hg h hr⟩
  | 18, _ => exact ⟨_, _, hat_new hb hn hi h hr⟩
  | 19, _ => exact ⟨_, _, hat_pubX h hr⟩
  | 20, _ => exact ⟨_, _, hat_local (by decide) (hc_local 20 (by decide)) rfl rfl hg h hr⟩
  | 21, _ => exact ⟨_, _, hat_local (by decide) (hc_local 21 (by decide)) rfl rfl hg h hr⟩
  | 22, _ => exact (hat_spawn h hr).elim
  | _ + 23, hk => omega

end Steps

/-- info: 'Spike.Lib.HelloPreTerm.hat_tstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hat_tstep

end Spike.Lib.HelloPreTerm
