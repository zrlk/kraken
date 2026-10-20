import WeakCore.TermSeenHid
import WeakCore.TermUndefZ

/-!
# TermUndefInv: `undefAt`, every protocol-word unit of a cell has an `undef` message

The global form `UndefAtG Eg mem` (the `SysInvN`/`SysInvW` clause `undefAt`):

* promise step: `EgP` keeps the cells and memory only grows (`undefAtG_prom`);
* thread step: `EgT` keeps the old cells, memory only grows, and a cell at a label the step
  allocated has its placeholders by `UndefNew` (`undefAtG_post`, `undefAtG_thread`);
* initially: no cells (`undefAtG_empty`, e.g. `TermInit.Eg0`);
* at the cut: `UndefAt` of any environment with the cut's cells (`undefAt_cut`), what
  `TermSeenHid.seenHid_of` needs.
-/

namespace TermUndefInv
open CoreLang CoreTerm TermRun TermSound TermStep TermCut TermSys TermMain TermUndefZ
open WeakMem (Msg Memory Address Ts AllocLabel)

theorem undefAtG_ext {Eg Eg' : GEnv} {mem mem' : Memory} (h : UndefAtG Eg mem)
    (hs : ∀ l c, Eg'.sto l = some c → Eg.sto l = some c)
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → mem'[t]? = some m) : UndefAtG Eg' mem' := by
  intro l c hc o n P hat hg
  obtain ⟨t, m, h1, h2, h3⟩ := h l c (hs l c hc) o n P hat hg
  exact ⟨t, m, hm t m h1, h2, h3⟩

theorem undefAtG_empty {Eg : GEnv} {mem : Memory} (h : ∀ l, Eg.sto l = none) : UndefAtG Eg mem := by
  intro l c hc
  rw [h l] at hc; cases hc

theorem memExt_get {m m' : Memory} (h : Promises.Sim.MemExt m m') :
    ∀ (t : Nat) (x : Msg), m[t]? = some x → m'[t]? = some x := by
  intro t x hx
  have hlt : t < m.size := (Array.getElem?_eq_some_iff.1 hx).1
  rw [h.get t hlt]; exact hx

theorem get_push {mem : Memory} {x : Msg} : ∀ (t : Nat) (m : Msg), mem[t]? = some m → (mem.push x)[t]? = some m := by
  intro t m h
  have hlt : t < mem.size := (Array.getElem?_eq_some_iff.1 h).1
  rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]; exact h

/-- **Promise step.** -/
theorem undefAtG_prom {Eg : GEnv} {mem : Memory} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    {j n : Nat} {x : Msg} (h : UndefAtG Eg mem) : UndefAtG (EgP Eg P N j n) (mem.push x) :=
  undefAtG_ext h (fun _ _ hc => hc) get_push

/-- **Thread step**, from the new cells' placeholders. -/
theorem undefAtG_post {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {c' : Cfg} {mem mem' : Memory}
    (h : UndefAtG Eg mem)
    (hnew : ∀ (l : AllocLabel) (c : Cell), FreshIn g n n' l → E'.sto l = some c →
      ∀ (o k : Nat) (P : Proto), AtOff c.ty o (.word (.lit k) P) → P.ghost = false →
        ∃ (t : Nat) (m : Msg), mem'[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val = .undef)
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → mem'[t]? = some m) :
    UndefAtG (EgT Eg g n n' E' c') mem' := by
  intro l c hc o k P hat hg
  simp only [EgT, GEnv.withFp, GEnv.post] at hc
  split at hc
  · rename_i hf
    exact hnew l c hf hc o k P hat hg
  · obtain ⟨t, m, h1, h2, h3⟩ := h l c hc o k P hat hg
    exact ⟨t, m, hm t m h1, h2, h3⟩

/-- **Thread step**, from `UndefNew`. -/
theorem undefAtG_thread {Eg : GEnv} {g : G} {s s' : St} {E' : TEnv} {c' : Cfg}
    (h : UndefAtG Eg s.mem) (hn : UndefNew g s s' E')
    (hm : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → s'.mem[t]? = some m) :
    UndefAtG (EgT Eg g s.nalloc s'.nalloc E' c') s'.mem :=
  undefAtG_post h hn hm

/-- **At the cut**: `UndefAt` of an environment with the cut's cells. -/
theorem undefAt_cut {Eg : GEnv} {i : Nat} {E' : TEnv} {mem : Memory} (h : UndefAtG Eg mem)
    (hs : E'.sto = cutSto Eg i) : TermSeenHid.UndefAt E' mem := by
  intro b n P hW
  obtain ⟨c, hc, hat, hg⟩ := hW
  rw [hs] at hc
  exact h b.label c (cutSto_sub hc) b.offset n P hat hg

end TermUndefInv

#print axioms TermUndefInv.undefAtG_ext
#print axioms TermUndefInv.undefAtG_empty
#print axioms TermUndefInv.undefAtG_prom
#print axioms TermUndefInv.undefAtG_post
#print axioms TermUndefInv.undefAtG_thread
#print axioms TermUndefInv.undefAt_cut
