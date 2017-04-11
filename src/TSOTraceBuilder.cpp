/* Copyright (C) 2014-2017 Carl Leonardsson
 *
 * This file is part of Nidhugg.
 *
 * Nidhugg is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Nidhugg is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include "Debug.h"
#include "TSOTraceBuilder.h"

#include <sstream>
#include <stdexcept>
#include <iostream>

TSOTraceBuilder::TSOTraceBuilder(const Configuration &conf) : TSOPSOTraceBuilder(conf) {
  threads.push_back(Thread(CPid(),{}));
  threads.push_back(Thread(CPS.new_aux(CPid()),{}));
  threads[1].available = false; // Store buffer is empty.
  prefix_idx = -1;
  dryrun = false;
  replay = false;
  last_full_memory_conflict = -1;
  last_md = 0;
}

TSOTraceBuilder::~TSOTraceBuilder(){
}

bool TSOTraceBuilder::schedule(int *proc, int *aux, int *alt, bool *dryrun){
  *dryrun = false;
  *alt = 0;
  this->dryrun = false;
  if(replay){
    /* Are we done with the current Event? */
    if(0 <= prefix_idx &&
       threads[curnode().iid.get_pid()].clock[curnode().iid.get_pid()] <
       curnode().iid.get_index() + curnode().size - 1){
      /* Continue executing the current Event */
      IPid pid = curnode().iid.get_pid();
      *proc = pid/2;
      *aux = pid % 2 - 1;
      *alt = 0;
      assert(threads[pid].available);
      ++threads[pid].clock[pid];
      return true;
    }else if(prefix_idx + 1 == int(prefix.size())){
      /* We are done replaying. Continue below... */
      replay = false;
    }else if(dry_sleepers < int(prefix[prefix_idx+1].sleep.size())){
      /* Before going to the next event, dry run the threads that are
       * being put to sleep.
       */
      IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers];
      ++dry_sleepers;
      threads[pid].sleeping = true;
      *proc = pid/2;
      *aux = pid % 2 - 1;
      *alt = 0;
      *dryrun = true;
      this->dryrun = true;
      return true;
    }else{
      /* Go to the next event. */
      dry_sleepers = 0;
      ++prefix_idx;
      IPid pid = curnode().iid.get_pid();
      *proc = pid/2;
      *aux = pid % 2 - 1;
      *alt = curnode().alt;
      assert(threads[pid].available);
      ++threads[pid].clock[pid];
      curnode().clock = threads[pid].clock;
      return true;
    }
  }

  assert(!replay);
  /* Create a new Event */

  /* Should we merge the last two events? */
  if(prefix.size() > 1 &&
     prefix[prefix.size()-1].iid.get_pid() == prefix[prefix.size()-2].iid.get_pid() &&
     !prefix[prefix.size()-1].may_conflict &&
     prefix[prefix.size()-1].sleep.empty()){
    assert(prefix[prefix.size()-1].branch.empty());
    assert(prefix[prefix.size()-1].wakeup.empty());
    ++prefix[prefix.size()-2].size;
    prefix.pop_back();
    --prefix_idx;
  }

  /* Before we schedule the new event. We should store the non available threads at this event.
   * This is important when adding conservative backtracking points.
   */
  if(prefix_idx > 0){
    for(unsigned k = 0; k < threads.size(); k++){
      if(!threads[k].available){
        prefix[prefix_idx-1].unavailable_threads.insert(k);
      }
    }
    prefix[prefix_idx-1].unavailable_threads.insert(threads.size());
  }

  /* Create a new Event */
  ++prefix_idx;
  assert(prefix_idx == int(prefix.size()));

  /* Find an available thread (auxiliary or real).
   *
   * Prioritize auxiliary before real, and older before younger
   * threads.
   */
  const unsigned sz = threads.size();
  unsigned p;

  /*get the current count from the previous prefix because a refused schedule might had happened
   */
  if(prefix_idx > 0)
    bound_cnt = prefix[prefix_idx-1].current_cnt;

  unsigned previous_id = prefix_idx ? prefix[prefix_idx - 1].iid.get_pid() : 0;
  bool is_previous_available = threads.size() > previous_id && prefix_idx ? threads[previous_id].available : false ;

  /*A reset may have caused an increase of the bound
   */

  if(conf.preemption_bound >=0 && bound_cnt > conf.preemption_bound){
        bound_blocked = true;
        return false;
      } 

retry:
  for(p = 1; p < sz; p += 2){ // Loop through auxiliary threads
    if(threads[p].available && !threads[p].sleeping &&
       (conf.max_search_depth < 0 || threads[p].clock[p] < conf.max_search_depth)){
      ++threads[p].clock[p];
      prefix.push_back(Event(IID<IPid>(IPid(p),threads[p].clock[p]),
                             threads[p].clock));

      *proc = p/2;
      assert(int(prefix_idx.size()) - 1 == prefix_idx);
      if(is_previous_available && p != previous_id)
      {
        bound_cnt++;
      }
      if(conf.preemption_bound >=0 && bound_cnt > conf.preemption_bound && conf.preem_method == Configuration::BPOR) {
        if(is_previous_available && p != previous_id)
          bound_cnt--;
        --threads[p].clock[p];
        prefix.pop_back();
        continue;
      }
      prefix[prefix_idx].current_cnt = bound_cnt;
      *aux = 0;
      return true;
    }
  }

  //Prioritize running thread
  if(prefix_idx>0 && conf.preemption_bound >=0 && conf.preem_method == Configuration::BPOR){
  // if(conf.preemption_bound >=0 && conf.preem_method == Configuration::BPOR){
    p = prefix[prefix_idx-1].iid.get_pid();
    if(threads[p].available && !threads[p].sleeping &&
       (conf.max_search_depth < 0 || threads[p].clock[p] < conf.max_search_depth)){
      ++threads[p].clock[p];
      prefix.push_back(Event(IID<IPid>(IPid(p),threads[p].clock[p]),
                             threads[p].clock));
      prefix[prefix_idx].current_cnt = bound_cnt;
      *proc = p/2;
      *aux = -1;
      return true;
    } 
  }


  for(p = 0; p < sz; p += 2){ // Loop through real threads

    if(threads[p].available && !threads[p].sleeping &&
       (conf.max_search_depth < 0 || threads[p].clock[p] < conf.max_search_depth)){
      ++threads[p].clock[p];
      prefix.push_back(Event(IID<IPid>(IPid(p),threads[p].clock[p]),
                             threads[p].clock));
      *proc = p/2;

      /* Increase the bound count if necessery (if the previous thread could run and the current thread is different)
       */

      if(is_previous_available && p != previous_id)
      {
        bound_cnt++;
      }

      /* If the bound was exceeded try to schedule anothor thread that won't increase the bound any more.
       * Most probably this will never be used because the current thread has the highest priority for scheduling.
       */

      if(conf.preemption_bound >=0 && bound_cnt > conf.preemption_bound && conf.preem_method == Configuration::BPOR) {
        if(is_previous_available && p != previous_id){
          bound_cnt--;
        }
        --threads[p].clock[p];
        prefix.pop_back();
        continue;
      }
      prefix[prefix_idx].current_cnt = bound_cnt;
      *aux = -1;

      /* Lets put all unavailable threads to the conservative set;
       */
      for(unsigned q; q < sz; q+=2){
        if(!threads[q].available)
          prefix[prefix_idx].conservative_branches.insert(q);
      }
      return true;
    }
  }


  /* This will be removed soon.
   * Force all the threads to wake up if no thread is available.
   * Conservative branching at the beginning of a thread block put threads to sleep set even though these threads were never
   * scheduled.
   * conservative_branches is better implementetion.
   */

  if(false && conf.preemption_bound >= 0 && conf.preem_method == Configuration::BPOR){


    for(p = 0; p < sz; p++){
      threads[p].sleeping = false;
      prefix[prefix_idx-1].wakeup.insert(p);
    }
    bool nobody_available = true;
    for(p = 0; p < sz && nobody_available; p++){
      if(threads[p].available)
        nobody_available = false;
    }
    if(!nobody_available){
      if(hard_reset_allowed <= 0){
        return false;
      }
      hard_reset_allowed--;
      goto retry;
    }
  }
  return false; // No available threads
}

void TSOTraceBuilder::refuse_schedule(){
  assert(prefix_idx == int(prefix.size())-1);
  assert(prefix.back().size == 1);
  assert(!prefix.back().may_conflict);
  assert(prefix.back().sleep.empty());
  assert(prefix.back().wakeup.empty());
  assert(prefix.back().branch.empty());
  IPid last_pid = prefix.back().iid.get_pid();
  prefix.pop_back();
  --prefix_idx;
  --threads[last_pid].clock[last_pid];
  mark_unavailable(last_pid/2,last_pid % 2 - 1);
}

void TSOTraceBuilder::mark_available(int proc, int aux){
  threads[ipid(proc,aux)].available = true;
}

void TSOTraceBuilder::mark_unavailable(int proc, int aux){
  threads[ipid(proc,aux)].available = false;
}

void TSOTraceBuilder::metadata(const llvm::MDNode *md){
  if(!dryrun && curnode().md == 0){
    curnode().md = md;
  }
  last_md = md;
}

bool TSOTraceBuilder::sleepset_is_empty() const{
  for(unsigned i = 0; i < threads.size(); ++i){
    if(threads[i].sleeping) return false;
  }
  return true;
}

bool TSOTraceBuilder::check_for_cycles(){
  IID<IPid> i_iid;
  if(!has_cycle(&i_iid)) return false;

  /* Report cycle */
  {
    assert(prefix.size());
    IID<CPid> c_iid(threads[i_iid.get_pid()].cpid,i_iid.get_index());
    errors.push_back(new RobustnessError(c_iid));
  }

  return true;
}

Trace *TSOTraceBuilder::get_trace() const{
  std::vector<IID<CPid> > cmp;
  std::vector<const llvm::MDNode*> cmp_md;
  std::vector<Error*> errs;
  for(unsigned i = 0; i < prefix.size(); ++i){
    cmp.push_back(IID<CPid>(threads[prefix[i].iid.get_pid()].cpid,prefix[i].iid.get_index()));
    cmp_md.push_back(prefix[i].md);
  };
  for(unsigned i = 0; i < errors.size(); ++i){
    errs.push_back(errors[i]->clone());
  }
  Trace *t = new IIDSeqTrace(cmp,cmp_md,errs);
  t->set_blocked(!sleepset_is_empty());
  return t;
}

bool TSOTraceBuilder::reset(){
  if(conf.debug_print_on_reset){
    llvm::dbgs() << " === TSOTraceBuilder reset ===\n";
    debug_print();
    llvm::dbgs() << " =============================\n";
  }

find_next_branch:
  int i;
  for(i = int(prefix.size())-1; 0 <= i; --i){
    /* Lets find out which treads where alive where the branch happened.
     * Assume that all threads were unavailable. 
     * At the position i if the bound count was increased then the thread at the position i-1 was available
     * Also if a thread was scheduled at the posotion i then it was available at the position i-1
     * It would be enough to do this only when a branch is found.
     */

    if( i > 0){
      threads[prefix[i-1].iid.get_pid()].available = false;
      if(prefix[i].current_cnt > prefix[i-1].current_cnt ||
        (prefix[i].current_cnt == prefix[i-1].current_cnt && prefix[i].iid.get_pid() == prefix[i-1].iid.get_pid())) {
        threads[prefix[i-1].iid.get_pid()].available = true;
      }
    }

    if(prefix[i].branch.size()){
      break;
    }
  }

  if(i < 0){
    /* No more branching is possible. */
    return false;
  }

  /* Setup the new Event at prefix[i] */
  {
next_branch:
int k;
Branch br = prefix[i].branch[0];

/* Ignore dpor branches if a conservative branch of the same thread exists at the beggining of the block.
 * There are logic errors here not fixed because this optimization didn't reduce the trace count.
 */

if(false && conf.preem_method == Configuration::BPOR){
  int current_proc = prefix[i].iid.get_pid();
  if(!br.is_conservative){
    // std::cout << "Not Conservative\n";
    for( k = i-1; k >=0 && current_proc == prefix[k].iid.get_pid(); k--){
      if(prefix[k].branch.size())
        break;
    }
    if(k>=0){
      int idx = prefix[k].branch.find(br);
      if(idx >=0 && prefix[k].branch[idx].is_conservative){
        prefix[i].branch.erase(br);
        if(prefix[i].branch.size())
          goto next_branch;
        else goto find_next_branch;
      }
    }
  }
}

    /* Find the index of br.pid. */
    int br_idx = 1;
    for(int j = i-1; br_idx == 1 && 0 <= j; --j){
      if(prefix[j].iid.get_pid() == br.pid){
        br_idx = prefix[j].iid.get_index() + prefix[j].size;
      }
    }

    /* Scheduling happens also here. So we have to take care of the bound count as well.
     */

    if(i>0){
      bound_cnt = prefix[i-1].current_cnt;
      if(prefix[i-1].iid.get_pid() != br.pid && threads[prefix[i-1].iid.get_pid()].available){
        bound_cnt++;
      }
    }

    Event evt(IID<IPid>(br.pid,br_idx),{});

    evt.alt = br.alt;
    evt.branch = prefix[i].branch;

    /* Conservative branches must be retained as long as the same prefix exists.
     */

    evt.conservative_branches = prefix[i].conservative_branches;
    evt.branch.erase(br);
    evt.sleep = prefix[i].sleep;

    /* Don't put to sleep set conservative branches (This eliminates the need for forced wake up).
     */

    if(br.pid != prefix[i].iid.get_pid()){
      if(conf.preemption_bound < 0 || !br.is_conservative)
        evt.sleep.insert(prefix[i].iid.get_pid());

      evt.conservative_branches.insert(br.pid);
      evt.conservative_branches.insert(prefix[i].iid.get_pid());
      
    } 

    evt.sleep_branch_trace_count =
      prefix[i].sleep_branch_trace_count + estimate_trace_count(i+1);

    prefix[i] = evt;
    //Yannis
    prefix[i].current_cnt = bound_cnt;

    prefix.resize(i+1,prefix[0]);
  }

  CPS = CPidSystem();
  threads.clear();
  threads.push_back(Thread(CPid(),{}));
  threads.push_back(Thread(CPS.new_aux(CPid()),{}));
  threads[1].available = false; // Store buffer is empty.
  mutexes.clear();
  cond_vars.clear();
  mem.clear();
  last_full_memory_conflict = -1;
  prefix_idx = -1;
  dryrun = false;
  replay = true;
  dry_sleepers = 0;
  last_md = 0;
  return true;
}

IID<CPid> TSOTraceBuilder::get_iid() const{
  IPid pid = curnode().iid.get_pid();
  int idx = curnode().iid.get_index();
  return IID<CPid>(threads[pid].cpid,idx);
}

static std::string rpad(std::string s, int n){
  while(int(s.size()) < n) s += " ";
  return s;
}

std::string TSOTraceBuilder::iid_string(const Event &evt) const{
  std::stringstream ss;
  ss << "(" << threads[evt.iid.get_pid()].cpid << "," << evt.iid.get_index();
  if(evt.size > 1){
    ss << "-" << evt.iid.get_index() + evt.size - 1;
  }
  ss << ")";
  if(evt.alt != 0){
    ss << "-alt:" << evt.alt;
  }
  return ss.str();
}

void TSOTraceBuilder::debug_print() const {
  llvm::dbgs() << "TSOTraceBuilder (debug print):\n";
  int iid_offs = 0;
  int clock_offs = 0;
  VecSet<IPid> sleep_set;
  for(unsigned i = 0; i < prefix.size(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    iid_offs = std::max(iid_offs,2*ipid+int(iid_string(prefix[i]).size()));
    clock_offs = std::max(clock_offs,int(prefix[i].clock.to_string().size()));
  }
  for(unsigned i = 0; i < prefix.size(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    llvm::dbgs() << rpad("",2+ipid*2)
                 << rpad(iid_string(prefix[i]),iid_offs-ipid*2)
                 << " " << rpad(prefix[i].clock.to_string(),clock_offs);
    sleep_set.insert(prefix[i].sleep);
    llvm::dbgs() << " SLP:{";
    for(int i = 0; i < sleep_set.size(); ++i){
      if(i != 0) llvm::dbgs() << ", ";
      llvm::dbgs() << threads[sleep_set[i]].cpid;
    }
    llvm::dbgs() << "}";
    if(conf.preemption_bound >=0)
      llvm::dbgs() << " BC:{" << prefix[i].current_cnt << "}";
    if(conf.preem_method == Configuration::BPOR){
      llvm::dbgs() << " CS:{";
      for(int j = 0; j < prefix[i].conservative_branches.size(); j++){
        if(j != 0 ) llvm::dbgs() << ", ";
        llvm::dbgs() << prefix[i].conservative_branches[j];
      }
      llvm::dbgs() << "}";
    }

    if(prefix[i].branch.size()){
      llvm::dbgs() << " branch: ";
      for(Branch b : prefix[i].branch){
        llvm::dbgs() << threads[b.pid].cpid << "("  << b.is_conservative <<")";
        if(b.alt != 0){
          llvm::dbgs() << "-alt:" << b.alt;
        }
        llvm::dbgs() << " ";
      }
    }
    llvm::dbgs() << "\n";
    for(IPid p : prefix[i].wakeup){
      sleep_set.erase(p);
    }
  }
  if(errors.size()){
    llvm::dbgs() << "Errors:\n";
    for(unsigned i = 0; i < errors.size(); ++i){
      llvm::dbgs() << "  Error #" << i+1 << ": "
                   << errors[i]->to_string() << "\n";
    }
  }
}

void TSOTraceBuilder::spawn(){
  IPid parent_ipid = curnode().iid.get_pid();
  CPid child_cpid = CPS.spawn(threads[parent_ipid].cpid);
  threads.push_back(Thread(child_cpid,threads[parent_ipid].clock));
  threads.push_back(Thread(CPS.new_aux(child_cpid),threads[parent_ipid].clock));
  threads.back().available = false; // Empty store buffer
}

void TSOTraceBuilder::store(const ConstMRef &ml){
  if(dryrun) return;
  IPid ipid = curnode().iid.get_pid();
  threads[ipid].store_buffer.push_back(PendingStore(ml,threads[ipid].clock,last_md));
  threads[ipid+1].available = true;
}

void TSOTraceBuilder::atomic_store(const ConstMRef &ml){
  if(dryrun){
  // std::cout << "atomic_store\n";
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    VecSet<void const*> &A = threads[pid].sleep_accesses_w;
    for(void const *b : ml){
      A.insert(b);
    }
    return;
  }
  IPid ipid = curnode().iid.get_pid();
  curnode().may_conflict = true;
  bool is_update = ipid % 2;

  IPid uipid = ipid; // ID of the thread changing the memory
  IPid tipid = is_update ? ipid-1 : ipid; // ID of the (real) thread that issued the store

  if(is_update){ // Add the clock of the store instruction
    assert(threads[tipid].store_buffer.size());
    const PendingStore &pst = threads[tipid].store_buffer.front();
    curnode().clock += pst.clock;
    threads[uipid].clock += pst.clock;
    curnode().origin_iid = IID<IPid>(tipid,pst.clock[tipid]);
    curnode().md = pst.md;
  }else{ // Add the clock of the auxiliary thread (because of fence semantics)
    assert(threads[tipid].store_buffer.empty());
    threads[tipid].clock += threads[tipid+1].clock;
    curnode().clock += threads[tipid+1].clock;
  }

  VecSet<int> seen_accesses;

  /* See previous updates reads to ml */
  for(void const *b : ml){
    ByteInfo &bi = mem[b];
    int lu = bi.last_update;
    assert(lu < int(prefix.size()));
    if(0 <= lu){
      IPid lu_tipid = 2*(prefix[lu].iid.get_pid() / 2);
      if(lu_tipid != tipid){
        seen_accesses.insert(bi.last_update);
      }
    }
    for(int i : bi.last_read){
      if(0 <= i && prefix[i].iid.get_pid() != tipid) seen_accesses.insert(i);
    }
  }

  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);

  /* Register in memory */
  for(void const *b : ml){
    ByteInfo &bi = mem[b];
    bi.last_update = prefix_idx;
    bi.last_update_ml = ml;
    if(is_update && threads[tipid].store_buffer.front().last_rowe >= 0){
      bi.last_read[tipid/2] = threads[tipid].store_buffer.front().last_rowe;
    }
    wakeup(Access::W,b);
  }

  if(is_update){ /* Remove pending store from buffer */
    for(unsigned i = 0; i < threads[tipid].store_buffer.size()-1; ++i){
      threads[tipid].store_buffer[i] = threads[tipid].store_buffer[i+1];
    }
    threads[tipid].store_buffer.pop_back();
    if(threads[tipid].store_buffer.empty()){
      threads[uipid].available = false;
    }
  }
}

void TSOTraceBuilder::load(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    VecSet<void const*> &A = threads[pid].sleep_accesses_r;
    for(void const *b : ml){
      A.insert(b);
    }
    return;
  }
  curnode().may_conflict = true;
  IPid ipid = curnode().iid.get_pid();

  /* Check if this is a ROWE */
  for(int i = int(threads[ipid].store_buffer.size())-1; 0 <= i; --i){
    if(threads[ipid].store_buffer[i].ml.ref == ml.ref){
      /* ROWE */
      threads[ipid].store_buffer[i].last_rowe = prefix_idx;
      return;
    }
  }

  /* Load from memory */

  VecSet<int> seen_accesses;

  /* See all updates to the read bytes. */
  for(void const *b : ml){
    int lu = mem[b].last_update;
    const ConstMRef &lu_ml = mem[b].last_update_ml;
    if(0 <= lu){
      IPid lu_tipid = 2*(prefix[lu].iid.get_pid() / 2);
      if(lu_tipid != ipid){
        seen_accesses.insert(lu);
      }else if(ml != lu_ml){
        const VClock<IPid> &clk = prefix[lu].clock;
        curnode().clock += clk;
        threads[ipid].clock += clk;
      }
    }
  }

  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);

  /* Register load in memory */
  for(void const *b : ml){
    mem[b].last_read[ipid/2] = prefix_idx;
    wakeup(Access::R,b);
  }
}

void TSOTraceBuilder::full_memory_conflict(){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_full_memory_conflict = true;
    return;
  }
  curnode().may_conflict = true;

  /* See all pervious memory accesses */
  VecSet<int> seen_accesses;
  for(auto it = mem.begin(); it != mem.end(); ++it){
    seen_accesses.insert(it->second.last_update);
    for(int i : it->second.last_read){
      seen_accesses.insert(i);
    }
  }
  for(auto it = mutexes.begin(); it != mutexes.end(); ++it){
    seen_accesses.insert(it->second.last_access);
  }
  seen_accesses.insert(last_full_memory_conflict);

  see_events(seen_accesses);

  wakeup(Access::W_ALL_MEMORY,0);
  last_full_memory_conflict = prefix_idx;

  /* No later access can have a conflict with any earlier access */
  mem.clear();
}

void TSOTraceBuilder::fence(){
  if(dryrun) return;
  IPid ipid = curnode().iid.get_pid();
  assert(ipid % 2 == 0);
  assert(threads[ipid].store_buffer.empty());
  curnode().clock += threads[ipid+1].clock;
  threads[ipid].clock += threads[ipid+1].clock;
}

void TSOTraceBuilder::join(int tgt_proc){
  if(dryrun) return;
  IPid ipid = curnode().iid.get_pid();
  curnode().clock += threads[tgt_proc*2].clock;
  threads[ipid].clock += threads[tgt_proc*2].clock;
  curnode().clock += threads[tgt_proc*2+1].clock;
  threads[ipid].clock += threads[tgt_proc*2+1].clock;
}

void TSOTraceBuilder::mutex_lock(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return;
  }
  fence();
  if(!conf.mutex_require_init && !mutexes.count(ml.ref)){
    // Assume static initialization
    mutexes[ml.ref] = Mutex();
  }
  assert(mutexes.count(ml.ref));
  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);

  Mutex &mutex = mutexes[ml.ref];
  IPid ipid = curnode().iid.get_pid();

  if(mutex.last_lock < 0){
    /* No previous lock */
    see_events({mutex.last_access,last_full_memory_conflict});
  }else{
    /* Register conflict with last preceding lock */
    if(!prefix[mutex.last_lock].clock.leq(curnode().clock)){
      add_branch(mutex.last_lock,prefix_idx,false);
    }
    curnode().clock += prefix[mutex.last_access].clock;
    threads[ipid].clock += prefix[mutex.last_access].clock;
    see_events({last_full_memory_conflict});
  }

  mutex.last_lock = mutex.last_access = prefix_idx;
}

void TSOTraceBuilder::mutex_lock_fail(const ConstMRef &ml){
  assert(!dryrun);
  if(!conf.mutex_require_init && !mutexes.count(ml.ref)){
    // Assume static initialization
    mutexes[ml.ref] = Mutex();
  }
  assert(mutexes.count(ml.ref));
  Mutex &mutex = mutexes[ml.ref];
  assert(0 <= mutex.last_lock);
  if(!prefix[mutex.last_lock].clock.leq(curnode().clock)){
    add_branch(mutex.last_lock,prefix_idx,false);
  }

  if(0 <= last_full_memory_conflict &&
     !prefix[last_full_memory_conflict].clock.leq(curnode().clock)){
    add_branch(last_full_memory_conflict,prefix_idx,false);
  }
}

void TSOTraceBuilder::mutex_trylock(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return;
  }
  fence();
  if(!conf.mutex_require_init && !mutexes.count(ml.ref)){
    // Assume static initialization
    mutexes[ml.ref] = Mutex();
  }
  assert(mutexes.count(ml.ref));
  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);
  Mutex &mutex = mutexes[ml.ref];
  see_events({mutex.last_access,last_full_memory_conflict});

  mutex.last_access = prefix_idx;
  if(mutex.last_lock < 0){ // Mutex is free
    mutex.last_lock = prefix_idx;
  }
}

void TSOTraceBuilder::mutex_unlock(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return;
  }
  fence();
  if(!conf.mutex_require_init && !mutexes.count(ml.ref)){
    // Assume static initialization
    mutexes[ml.ref] = Mutex();
  }
  assert(mutexes.count(ml.ref));
  Mutex &mutex = mutexes[ml.ref];
  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);
  assert(0 <= mutex.last_access);

  see_events({mutex.last_access,last_full_memory_conflict});

  mutex.last_access = prefix_idx;
}

void TSOTraceBuilder::mutex_init(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return;
  }
  fence();
  assert(mutexes.count(ml.ref) == 0);
  curnode().may_conflict = true;
  mutexes[ml.ref] = Mutex(prefix_idx);
  see_events({last_full_memory_conflict});
}

void TSOTraceBuilder::mutex_destroy(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return;
  }
  fence();
  if(!conf.mutex_require_init && !mutexes.count(ml.ref)){
    // Assume static initialization
    mutexes[ml.ref] = Mutex();
  }
  assert(mutexes.count(ml.ref));
  Mutex &mutex = mutexes[ml.ref];
  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);

  see_events({mutex.last_access,last_full_memory_conflict});

  mutexes.erase(ml.ref);
}

bool TSOTraceBuilder::cond_init(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return true;
  }
  fence();
  if(cond_vars.count(ml.ref)){
    pthreads_error("Condition variable initiated twice.");
    return false;
  }
  curnode().may_conflict = true;
  cond_vars[ml.ref] = CondVar(prefix_idx);
  see_events({last_full_memory_conflict});
  return true;
}

bool TSOTraceBuilder::cond_signal(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return true;
  }
  fence();
  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);

  auto it = cond_vars.find(ml.ref);
  if(it == cond_vars.end()){
    pthreads_error("cond_signal called with uninitialized condition variable.");
    return false;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {last_full_memory_conflict};
  if(curnode().alt < int(cond_var.waiters.size())-1){
    assert(curnode().alt == 0);
    register_alternatives(cond_var.waiters.size());
  }
  assert(0 <= curnode().alt);
  assert(cond_var.waiters.empty() || curnode().alt < int(cond_var.waiters.size()));
  if(cond_var.waiters.size()){
    /* Wake up the alt:th waiter. */
    int i = cond_var.waiters[curnode().alt];
    assert(0 <= i && i < prefix_idx);
    IPid ipid = prefix[i].iid.get_pid();
    assert(!threads[ipid].available);
    threads[ipid].available = true;
    /* The next instruction by the thread ipid should be ordered after
     * this signal.
     */
    threads[ipid].clock += curnode().clock;
    seen_events.insert(i);

    /* Remove waiter from cond_var.waiters */
    for(int j = curnode().alt; j < int(cond_var.waiters.size())-1; ++j){
      cond_var.waiters[j] = cond_var.waiters[j+1];
    }
    cond_var.waiters.pop_back();
  }
  cond_var.last_signal = prefix_idx;

  see_events(seen_events);

  return true;
}

bool TSOTraceBuilder::cond_broadcast(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return true;
  }
  fence();
  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);

  auto it = cond_vars.find(ml.ref);
  if(it == cond_vars.end()){
    pthreads_error("cond_broadcast called with uninitialized condition variable.");
    return false;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {last_full_memory_conflict};
  for(int i : cond_var.waiters){
    assert(0 <= i && i < prefix_idx);
    IPid ipid = prefix[i].iid.get_pid();
    assert(!threads[ipid].available);
    threads[ipid].available = true;
    /* The next instruction by the thread ipid should be ordered after
     * this broadcast.
     */
    threads[ipid].clock += curnode().clock;
    seen_events.insert(i);
  }
  cond_var.waiters.clear();
  cond_var.last_signal = prefix_idx;

  see_events(seen_events);

  return true;
}

bool TSOTraceBuilder::cond_wait(const ConstMRef &cond_ml, const ConstMRef &mutex_ml){
  {
    auto it = mutexes.find(mutex_ml.ref);
    if(!dryrun && it == mutexes.end()){
      if(conf.mutex_require_init){
        pthreads_error("cond_wait called with uninitialized mutex object.");
      }else{
        pthreads_error("cond_wait called with unlocked mutex object.");
      }
      return false;
    }
    Mutex &mtx = it->second;
    if(!dryrun && (mtx.last_lock < 0 || prefix[mtx.last_lock].iid.get_pid() != curnode().iid.get_pid())){
      pthreads_error("cond_wait called with mutex which is not locked by the same thread.");
      return false;
    }
  }

  mutex_unlock(mutex_ml);
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_r.insert(cond_ml.ref);
    return true;
  }
  fence();
  curnode().may_conflict = true;
  wakeup(Access::R,cond_ml.ref);

  IPid pid = curnode().iid.get_pid();

  auto it = cond_vars.find(cond_ml.ref);
  if(it == cond_vars.end()){
    pthreads_error("cond_wait called with uninitialized condition variable.");
    return false;
  }
  it->second.waiters.push_back(prefix_idx);
  threads[pid].available = false;

  see_events({last_full_memory_conflict,it->second.last_signal});

  return true;
}

int TSOTraceBuilder::cond_destroy(const ConstMRef &ml){
  if(dryrun){
    assert(prefix_idx+1 < int(prefix.size()));
    assert(dry_sleepers <= prefix[prefix_idx+1].sleep.size());
    IPid pid = prefix[prefix_idx+1].sleep[dry_sleepers-1];
    threads[pid].sleep_accesses_w.insert(ml.ref);
    return 0;
  }
  fence();

  int err = (EBUSY == 1) ? 2 : 1; // Chose an error value different from EBUSY

  curnode().may_conflict = true;
  wakeup(Access::W,ml.ref);

  auto it = cond_vars.find(ml.ref);
  if(it == cond_vars.end()){
    pthreads_error("cond_destroy called on uninitialized condition variable.");
    return err;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {cond_var.last_signal,last_full_memory_conflict};
  for(int i : cond_var.waiters) seen_events.insert(i);
  see_events(seen_events);

  int rv = cond_var.waiters.size() ? EBUSY : 0;
  cond_vars.erase(ml.ref);
  return rv;
}


bool TSOTraceBuilder::canRunThisInstruction(){
  int a = conf.preemption_bound;
  if(a < 0) return true;
  return (!this->dryrun);
  
}

void TSOTraceBuilder::register_alternatives(int alt_count){
  curnode().may_conflict = true;
  for(int i = curnode().alt+1; i < alt_count; ++i){
    curnode().branch.insert(Branch({curnode().iid.get_pid(),i}));
  }
}

VecSet<TSOTraceBuilder::IPid> TSOTraceBuilder::sleep_set_at(int i){
  VecSet<IPid> sleep;
  for(int j = 0; j < i; ++j){
    sleep.insert(prefix[j].sleep);
    for(auto it = prefix[j].wakeup.begin(); it != prefix[j].wakeup.end(); ++it){
      sleep.erase(*it);
    }
  }
  sleep.insert(prefix[i].sleep);
  return sleep;
}

// void TSOTraceBuilder::see_events(const VecSet<int> &seen_accesses){// Finding I set or WI 
//   /* Register new branches */
//   std::vector<int> branch;
//   for(int i : seen_accesses){
//     if(i < 0) continue;
//     const VClock<IPid> &iclock = prefix[i].clock;
//     // This event happens before current event
//     if(iclock.leq(curnode().clock)) continue;
//     // there is another event happening before this one (not the current one)
//     if(std::any_of(seen_accesses.begin(),seen_accesses.end(),
//                    [i,&iclock,this](int j){
//                      return 0 <= j && i != j && iclock.leq(this->prefix[j].clock);
//                    })) continue;
//     branch.push_back(i);
//   }

//   /* Add clocks from seen accesses */
//   IPid ipid = curnode().iid.get_pid();
//   for(int i : seen_accesses){
//     if(i < 0) continue;
//     assert(0 <= i && i <= prefix_idx);
//     curnode().clock += prefix[i].clock;
//     threads[ipid].clock += prefix[i].clock;
//   }

//   for(int i : branch){
//     add_branch(i,prefix_idx);
//   }
// }


void TSOTraceBuilder::see_events(const VecSet<int> &seen_accesses){// Finding I set or WI 
  /* Register new branches */
  std::vector<int> branch;
  std::vector<bool> is_conservative_branch;
  int idx_seen_accesses = -1;
  for(int i : seen_accesses){
    idx_seen_accesses++;
    if(i < 0) continue;
    const VClock<IPid> &iclock = prefix[i].clock;
    // This event happens before current event
    if(iclock.leq(curnode().clock)) continue;
    // there is another event happening before this one (not the current one)
    if(std::any_of(seen_accesses.begin(),seen_accesses.end(),
                   [i,&iclock,this](int j){
                     return 0 <= j && i != j && iclock.leq(this->prefix[j].clock);
                   })) continue;
    branch.push_back(i);
    /* Create a boolean vector in parallel with the branch vector indicating if the suggested branch is conservative or not.
     */

    is_conservative_branch.push_back(false);
    int current_proc = prefix[i].iid.get_pid();
    int k;

    /* Try to add a branch at the beginning of the thread block where the collision happens.
     * The thread put to branch should be available (or just exist) at the beggining of the block.
     */
    if(conf.preemption_bound >= 0 && conf.preem_method ==Configuration::BPOR && conf.memory_model == Configuration::SC){
    // if(false){
      bool broken = false;
      for(k = i-1; k>=0 && current_proc == prefix[k].iid.get_pid();   k--){
        if(idx_seen_accesses && seen_accesses[idx_seen_accesses-1] == k){
          broken = true;
          break;
        }
      }
      if(broken)
        continue;

      /* Add conservative branches to branch.
       */

      // Try to add either conservative or not conservative traces
      if(k > -1 && k+1!=i && current_proc != prefix[k].iid.get_pid()){ // && !prefix[k+1].conservative_branches.count(current_proc)){
      // if(k > -1 && k+1!=i && current_proc != prefix[k].iid.get_pid() && !prefix[k+1].conservative_branches.count(current_proc)
         // && seen_accesses[idx_seen_accesses-1] <= k){
        assert(prefix_idx < prefix.size());
        // if(current_proc != prefix[k].iid.get_pid())
          // branch[branch.size()-1] = k+1;
          // is_conservative_branch[is_conservative_branch.size()-1] = true;
           branch.push_back(k+1);
           is_conservative_branch.push_back(true);
          // std::cout<< "Adding backtrack2 to " << k+1 << "\n";
      } 
   }
     
  }

  /* Add clocks from seen accesses */
  IPid ipid = curnode().iid.get_pid();
  for(int i : seen_accesses){
    if(i < 0) continue;
    assert(0 <= i && i <= prefix_idx);
    curnode().clock += prefix[i].clock;
    threads[ipid].clock += prefix[i].clock;
  }

  int index = 0; 
  for(int i : branch){
    add_branch(i,prefix_idx,is_conservative_branch[index++]);
  } 

}


void TSOTraceBuilder::add_branch(int i, int j, bool is_conservative){
  assert(0 <= i);
  assert(i < j);
  assert(j <= prefix_idx);

  

  VecSet<IPid> isleep = sleep_set_at(i);
  /* candidates is a map from IPid p to event index i such that the
   * IID (p,i) identifies an event between prefix[i] (exclusive) and
   * prefix[j] (inclusive) such that (p,i) does not happen-after any
   * other IID between prefix[i] (inclusive) and prefix[j]
   * (inclusive).
   *
   * If no such event has yet been found for a thread p, then
   * candidates[p] is out of bounds, or has the value -1.
   */

  // Don't add conservative branch if there is already a branch
  // if(is_conservative && prefix[i].branch.size()) return;

  std::vector<int> candidates;
  Branch cand = {-1,0,is_conservative};
  const VClock<IPid> &iclock = prefix[i].clock;
  for(int k = i+1; k <= j; ++k){
    IPid p = prefix[k].iid.get_pid();
    /* Did we already cover p? */
    if(p < int(candidates.size()) && 0 <= candidates[p]) continue;
    const VClock<IPid> &pclock = prefix[k].clock;
    /* Is p after prefix[i]? */
    if(k != j && iclock.leq(pclock)) continue;
    /* Is p after some other candidate? */
    bool is_after = false;
    for(int q = 0; !is_after && q < int(candidates.size()); ++q){
      if(0 <= candidates[q] && candidates[q] <= pclock[q]){
        is_after = true;
      }
    }
    if(is_after) continue;
    if(int(candidates.size()) <= p){
      candidates.resize(p+1,-1);
    }
    candidates[p] = prefix[k].iid.get_index();
    cand.pid = p;

    if(prefix[i].branch.count(cand)){ //|| prefix[i].branch.count({cand.pid,cand.alt,!(cand.is_conservative)})){
      /* There is already a satisfactory candidate branch */
       int bid = prefix[i].branch.find(cand);

       /* Update the conservative branches with the non conservative ones.
        */

       if(prefix[i].branch[bid].is_conservative){
         if(cand.is_conservative && !is_conservative){
           prefix[i].branch.insert(cand);
         }
       }
      return;
    }
    if(isleep.count(cand.pid)){
      /* This candidate is already sleeping (has been considered) at
       * prefix[i]. */
      return;
    }

    /* Be more strict with conservative branches.
     * Reject a branch if is already in the conservative set.
     */
    // added is_conservative at the beggining..
    // I should think about it.
    if(is_conservative && conf.preemption_bound >=0 && conf.preem_method == Configuration::BPOR){
      if(prefix[i].conservative_branches.count(cand.pid)){ // Should i check for conservativity???
      /* This branch has already been considered
       */
      return;
    }

    /* Reject branch if the thread was unavailable at that position
     */
    if(is_conservative && prefix[i].unavailable_threads.size()){ 
        if(prefix[i].unavailable_threads.count(cand.pid) || prefix[i].unavailable_threads.back() <= cand.pid){
            return;
        }
      }

    if(i && prefix[i-1].branch.count(cand)){
        prefix[i].conservative_branches.insert(cand.pid);
        return;
      }
  }

  }

  /* Count the number of branches rejected by the bound.
   */
  
  if(i > 0 && conf.preemption_bound >=0){
    bool interrupting_someone = prefix[i].iid.get_pid() == prefix[i-1].iid.get_pid();
    if(interrupting_someone && prefix[i].current_cnt == conf.preemption_bound){
      branches_rejected++;
      return;
    }
  }

  assert(0 <= cand.pid);
  // std::cout << "New candidate added \n";

  prefix[i].branch.insert(cand);

  //Since a conservative branch is added lets remove it from above
  // if(cand.is_conservative){
  //   if(i>0){
  //     prefix[i-1].branch.erase(cand);
  //   }
  // }
}

bool TSOTraceBuilder::has_pending_store(IPid pid, void const *ml) const {
  const std::vector<PendingStore> &sb = threads[pid].store_buffer;
  for(unsigned i = 0; i < sb.size(); ++i){
    if(sb[i].ml.includes(ml)){
      return true;
    }
  }
  return false;
}

void TSOTraceBuilder::wakeup(Access::Type type, void const *ml){
  IPid pid = curnode().iid.get_pid();
  std::vector<IPid> wakeup; // Wakeup these
  switch(type){
  case Access::W_ALL_MEMORY:
    {
      for(unsigned p = 0; p < threads.size(); ++p){
        if(threads[p].sleep_full_memory_conflict ||
           threads[p].sleep_accesses_w.size()){
          wakeup.push_back(p);
        }else{
          for(void const *b : threads[p].sleep_accesses_r){
            if(!has_pending_store(p,b)){
              wakeup.push_back(p);
              break;
            }
          }
        }
      }
      break;
    }
  case Access::R:
    {
      for(unsigned p = 0; p < threads.size(); ++p){
        if(threads[p].sleep_full_memory_conflict ||
           (int(p) != pid+1 &&
            threads[p].sleep_accesses_w.count(ml))){
          wakeup.push_back(p);
        }
      }
      break;
    }
  case Access::W:
    {
      // std::cout << "Waking up for write access...\n";
      for(unsigned p = 0; p < threads.size(); ++p){
        if(threads[p].sleep_full_memory_conflict ||
           (int(p) + 1 != pid &&
            (threads[p].sleep_accesses_w.count(ml) ||
             (threads[p].sleep_accesses_r.count(ml) &&
              !has_pending_store(p,ml))))){
          wakeup.push_back(p);
        }
      }
      break;
    }
  default:
    throw std::logic_error("TSOTraceBuilder::wakeup: Unknown type of memory access.");
  }

  for(IPid p : wakeup){
    assert(threads[p].sleeping);
    threads[p].sleep_accesses_r.clear();
    threads[p].sleep_accesses_w.clear();
    threads[p].sleep_full_memory_conflict = false;
    threads[p].sleeping = false;
    curnode().wakeup.insert(p);
  }
}

bool TSOTraceBuilder::has_cycle(IID<IPid> *loc) const{
  int proc_count = threads.size();
  int pfx_size = prefix.size();

  /* Identify all store events */
  struct stupd_t{
    /* The index part of the IID identifying a store event. */
    int store;
    /* The index in prefix of the corresponding update event. */
    int update;
  };
  /* stores[proc] is all store events of process proc, ordered by
   * store index.
   */
  std::vector<std::vector<stupd_t> > stores(proc_count);
  for(int i = 0; i < pfx_size; ++i){
    if(prefix[i].iid.get_pid() % 2){ // Update
      assert(prefix[i].origin_iid.get_pid() == prefix[i].iid.get_pid()-1);
      stores[prefix[i].iid.get_pid() / 2].push_back({prefix[i].origin_iid.get_index(),i});
    }
  }

  /* Attempt to replay computation under SC */
  struct proc_t {
    proc_t()
      : pc(0), pfx_index(0), store_index(0), blocked(false), block_clock() {};
    int pc; // Current program counter
    int pfx_index; // Index into prefix
    int store_index; // Index into stores
    bool blocked; // Is the process currently blocked?
    VClock<IPid> block_clock; // If blocked, what are we waiting for?
  };
  std::vector<proc_t> procs(proc_count);

  int proc = 0; // The next scheduled process
  /* alive keeps track of whether any process has been successfully
   * scheduled lately
   */
  bool alive = false;
  while(true){
    // Advance pfx_index to the right Event in prefix
    while(procs[proc].pfx_index < pfx_size &&
          prefix[procs[proc].pfx_index].iid.get_pid() != proc*2){
      ++procs[proc].pfx_index;
    }
    if(pfx_size <= procs[proc].pfx_index){
      // This process is finished
      proc = (proc+1)%proc_count;
      if(proc == 0){
        if(!alive) break;
        alive = false;
      }
      continue;
    }

    int next_pc = procs[proc].pc+1;
    const Event &evt = prefix[procs[proc].pfx_index];

    if(!procs[proc].blocked){
      assert(evt.iid.get_pid() == 2*proc);
      assert(evt.iid.get_index() <= next_pc);
      assert(next_pc < evt.iid.get_index() + evt.size);
      procs[proc].block_clock = evt.clock;
      assert(procs[proc].block_clock[proc*2] <= next_pc);
      procs[proc].block_clock[proc*2] = next_pc;
      if(procs[proc].store_index < int(stores[proc].size()) &&
         stores[proc][procs[proc].store_index].store == next_pc){
        // This is a store. Also consider the update's clock.
        procs[proc].block_clock += prefix[stores[proc][procs[proc].store_index].update].clock;
        ++procs[proc].store_index;
      }
    }

    // Is this process blocked?
    // Is there some process we have to wait for?
    {
      int i;
      procs[proc].blocked = false;
      for(i = 0; i < proc_count; ++i){
        if(i != proc && procs[i].pc < procs[proc].block_clock[i*2]){
          procs[proc].blocked = true;
          break;
        }
      }
    }

    // Are we still blocked?
    if(procs[proc].blocked){
      proc = (proc+1)%proc_count; // Try another process
      if(proc == 0){
        if(!alive) break;
        alive = false;
      }
    }else{
      alive = true;
      procs[proc].pc = next_pc;
      assert(next_pc == procs[proc].block_clock[proc*2]);

      // Advance pc to next interesting event
      next_pc = evt.iid.get_index() + evt.size - 1;
      if(procs[proc].store_index < int(stores[proc].size()) &&
         stores[proc][procs[proc].store_index].store-1 < next_pc){
        next_pc = stores[proc][procs[proc].store_index].store-1;
      }
      assert(procs[proc].pc <= next_pc);
      procs[proc].pc = next_pc;

      if(next_pc + 1 == evt.iid.get_index() + evt.size){
        // We are done with this Event
        ++procs[proc].pfx_index;
      }
    }
  }

  // Did all processes finish, or are some still blocked?
  {
    int upd_idx = -1; // Index of the latest update involved in a cycle
    bool has_cycle = false;
    for(int i = 0; i < proc_count; ++i){
      if(procs[i].blocked){
        // There is a cycle
        has_cycle = true;
        int next_pc = procs[i].pc+1;
        if(0 < procs[i].store_index && stores[i][procs[i].store_index-1].store == next_pc){
          if(stores[i][procs[i].store_index-1].update > upd_idx){
            upd_idx = stores[i][procs[i].store_index-1].update;
            *loc = prefix[upd_idx].iid;
          }
        }
      }
    }
    assert(!has_cycle || 0 <= upd_idx);
    return has_cycle;
  }
}

int TSOTraceBuilder::estimate_trace_count() const{
  return estimate_trace_count(0);
}

int TSOTraceBuilder::estimate_trace_count(int idx) const{
  if(idx > int(prefix.size())) return 0;
  if(idx == int(prefix.size())) return 1;

  int count = 1;
  for(int i = int(prefix.size())-1; idx <= i; --i){
    count += prefix[i].sleep_branch_trace_count;
    count += prefix[i].branch.size()*(count / (1 + prefix[i].sleep.size()));
  }

  return count;
}