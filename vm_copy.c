#include "param.h"
#include "types.h"
#include "defs.h"
#include "x86.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "elf.h"
#include "spinlock.h"

struct swap_slot {
  int page_perm[NPROC];  
  int is_free;
  int arr[NPROC];
  int fill[NPROC];
  pte_t* pte_entry[NPROC];
};

#define NSLOTS SWAPBLOCKS/8
struct swap_slot sblocks[SWAPBLOCKS/8];

void init_swap(){
  for(int i=0; i<NSLOTS; i++){
    sblocks[i].is_free = 1;
    for(int j=0; j<NPROC; j++){
      sblocks[i].fill[j]=1;
    }
  }
}





extern char data[];  // defined by kernel.ld
pde_t *kpgdir;  // for use in scheduler()

// Set up CPU's kernel segment descriptors.
// Run once on entry on each CPU.
void
seginit(void)
{
  struct cpu *c;

  // Map "logical" addresses to virtual addresses using identity map.
  // Cannot share a CODE descriptor for both kernel and user
  // because it would have to have DPL_USR, but the CPU forbids
  // an interrupt from CPL=0 to DPL=3.
  c = &cpus[cpuid()];
  c->gdt[SEG_KCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, 0);
  c->gdt[SEG_KDATA] = SEG(STA_W, 0, 0xffffffff, 0);
  c->gdt[SEG_UCODE] = SEG(STA_X|STA_R, 0, 0xffffffff, DPL_USER);
  c->gdt[SEG_UDATA] = SEG(STA_W, 0, 0xffffffff, DPL_USER);
  lgdt(c->gdt, sizeof(c->gdt));
}

// Return the address of the PTE in page table pgdir
// that corresponds to virtual address va.  If alloc!=0,
// create any required page table pages.
static pte_t *
walkpgdir(pde_t *pgdir, const void *va, int alloc)
{
  pde_t *pde;
  pte_t *pgtab;

  pde = &pgdir[PDX(va)];
  if(*pde & PTE_P){
    pgtab = (pte_t*)P2V(PTE_ADDR(*pde));
  } else {
    if(!alloc || (pgtab = (pte_t*)kalloc()) == 0)
      return 0;
    // Make sure all those PTE_P bits are zero.
    memset(pgtab, 0, PGSIZE);
    // The permissions here are overly generous, but they can
    // be further restricted by the permissions in the page table
    // entries, if necessary.
    *pde = V2P(pgtab) | PTE_P | PTE_W | PTE_U;
  }
  return &pgtab[PTX(va)];
}

// Create PTEs for virtual addresses starting at va that refer to
// physical addresses starting at pa. va and size might not
// be page-aligned.
static int
mappages(pde_t *pgdir, void *va, uint size, uint pa, int perm)
{
  char *a, *last;
  pte_t *pte;

  a = (char*)PGROUNDDOWN((uint)va);
  last = (char*)PGROUNDDOWN(((uint)va) + size - 1);
  for(;;){
    if((pte = walkpgdir(pgdir, a, 1)) == 0)
      return -1;
    if(*pte & PTE_P)
      panic("remap");
    *pte = pa | perm | PTE_P;
    if(a == last)
      break;
    a += PGSIZE;
    pa += PGSIZE;
  }
  return 0;
}

struct rmap{
    struct spinlock lock;
    uint pg_ref_count;
    pte_t* pid_arr[NPROC];
    int fill[NPROC];
};

struct rmap rev_map[PHYSTOP/PGSIZE];

void rev_init(){
  cprintf("IN rev_init\n");
    for(int i=0; i<PHYSTOP/PGSIZE; i++){
    rev_map[i].pg_ref_count=0;
    for(int j=0; j<NPROC; j++){
      // rev_map[i].pid_arr[j]=-1;
      rev_map[i].fill[j]=-1;
    }
    initlock(&(rev_map[i].lock),"rmap");
  }
}

void incre_rev_map(uint pa, pte_t* pte){
    cprintf("IN increment\n");
    acquire(&(rev_map[pa/PGSIZE].lock));
    rev_map[pa/PGSIZE].pg_ref_count+=1;
    int ind=-1;
    for(int i=0; i<NPROC; i++){
      if (rev_map[pa/PGSIZE].fill[i]==-1){
        ind=i;
        break;
      }
    }
    rev_map[pa/PGSIZE].pid_arr[ind]=pte;
    rev_map[pa/PGSIZE].fill[ind]=1;
    release(&(rev_map[pa/PGSIZE].lock));
    return;
}

void decre_rev_map(uint pa, pte_t* pte){
   if (*pte & PTE_S){
      for(int i=0; i<NSLOTS; i++){
        if (sblocks[i].is_free==0){
          for(int j=0; j<NPROC; j++){
            if (sblocks[i].fill[j]==0 && sblocks[i].pte_entry[j]==pte){
              sblocks[i].fill[j]=1;
              sblocks[i].is_free=1;
            }
          }
        }
      }
      return;
   }
    cprintf("IN DECREMENT\n");
    acquire(&(rev_map[pa/PGSIZE].lock));
    rev_map[pa/PGSIZE].pg_ref_count-=1;
    int ind=-1;
    for(int i=0; i<NPROC; i++){
      if (rev_map[pa/PGSIZE].pid_arr[i]==pte && rev_map[pa/PGSIZE].fill[i]==1){
        ind=i;
        break;
      }
    }
    char *v = P2V(pa);
    if (rev_map[pa/PGSIZE].pg_ref_count<=0){
      kfree(v);
    }
    rev_map[pa/PGSIZE].fill[ind]=-1;
    release(&(rev_map[pa/PGSIZE].lock));
    return;
}

// There is one page table per process, plus one that's used when
// a CPU is not running any process (kpgdir). The kernel uses the
// current process's page table during system calls and interrupts;
// page protection bits prevent user code from using the kernel's
// mappings.
//
// setupkvm() and exec() set up every page table like this:
//
//   0..KERNBASE: user memory (text+data+stack+heap), mapped to
//                phys memory allocated by the kernel
//   KERNBASE..KERNBASE+EXTMEM: mapped to 0..EXTMEM (for I/O space)
//   KERNBASE+EXTMEM..data: mapped to EXTMEM..V2P(data)
//                for the kernel's instructions and r/o data
//   data..KERNBASE+PHYSTOP: mapped to V2P(data)..PHYSTOP,
//                                  rw data + free physical memory
//   0xfe000000..0: mapped direct (devices such as ioapic)
//
// The kernel allocates physical memory for its heap and for user memory
// between V2P(end) and the end of physical memory (PHYSTOP)
// (directly addressable from end..P2V(PHYSTOP)).

// This table defines the kernel's mappings, which are present in
// every process's page table.
static struct kmap {
  void *virt;
  uint phys_start;
  uint phys_end;
  int perm;
} kmap[] = {
 { (void*)KERNBASE, 0,             EXTMEM,    PTE_W}, // I/O space
//  { (void*)KERNLINK, V2P(KERNLINK), V2P(data), 0},     // kern text+rodata
//  { (void*)data,     V2P(data),     PHYSTOP,   PTE_W}, // kern data+memory
 { (void*)DEVSPACE, DEVSPACE,      0,         PTE_W}, // more devices
};

// Set up kernel part of a page table.
pde_t*
setupkvm(void)
{
  pde_t *pgdir;
  struct kmap *k;

  if((pgdir = (pde_t*)kalloc()) == 0)
    return 0;
  memset(pgdir, 0, PGSIZE);
  if (P2V(PHYSTOP) > (void*)DEVSPACE)
    panic("PHYSTOP too high");
  for(k = kmap; k < &kmap[NELEM(kmap)]; k++)
    if(mappages(pgdir, k->virt, k->phys_end - k->phys_start,
                (uint)k->phys_start, k->perm) < 0) {
      freevm(pgdir);
      return 0;
    }
  return pgdir;
}

// Allocate one page table for the machine for the kernel address
// space for scheduler processes.
void
kvmalloc(void)
{
  kpgdir = setupkvm();
  switchkvm();
}

// Switch h/w page table register to the kernel-only page table,
// for when no process is running.
void
switchkvm(void)
{
  lcr3(V2P(kpgdir));   // switch to the kernel page table
}

// Switch TSS and h/w page table to correspond to process p.
void
switchuvm(struct proc *p)
{
  if(p == 0)
    panic("switchuvm: no process");
  if(p->kstack == 0)
    panic("switchuvm: no kstack");
  if(p->pgdir == 0)
    panic("switchuvm: no pgdir");

  pushcli();
  mycpu()->gdt[SEG_TSS] = SEG16(STS_T32A, &mycpu()->ts,
                                sizeof(mycpu()->ts)-1, 0);
  mycpu()->gdt[SEG_TSS].s = 0;
  mycpu()->ts.ss0 = SEG_KDATA << 3;
  mycpu()->ts.esp0 = (uint)p->kstack + KSTACKSIZE;
  // setting IOPL=0 in eflags *and* iomb beyond the tss segment limit
  // forbids I/O instructions (e.g., inb and outb) from user space
  mycpu()->ts.iomb = (ushort) 0xFFFF;
  ltr(SEG_TSS << 3);
  lcr3(V2P(p->pgdir));  // switch to process's address space
  popcli();
}

// Load the initcode into address 0 of pgdir.
// sz must be less than a page.
void
inituvm(pde_t *pgdir, char *init, uint sz)
{
  char *mem;

  if(sz >= PGSIZE)
    panic("inituvm: more than a page");
  mem = kalloc();
  memset(mem, 0, PGSIZE);
  mappages(pgdir, 0, PGSIZE, V2P(mem), PTE_W|PTE_U);
  memmove(mem, init, sz);
  pte_t* x=walkpgdir(pgdir,(void*)0,0);
  incre_rev_map(V2P(mem),x);
  cprintf("init %d\n",V2P(mem));
}

// Load a program segment into pgdir.  addr must be page-aligned
// and the pages from addr to addr+sz must already be mapped.
int
loaduvm(pde_t *pgdir, char *addr, struct inode *ip, uint offset, uint sz)
{
  uint i, pa, n;
  pte_t *pte;

  if((uint) addr % PGSIZE != 0)
    panic("loaduvm: addr must be page aligned");
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, addr+i, 0)) == 0)
      panic("loaduvm: address should exist");
    pa = PTE_ADDR(*pte);
    if(sz - i < PGSIZE)
      n = sz - i;
    else
      n = PGSIZE;
    if(readi(ip, P2V(pa), offset+i, n) != n)
      return -1;
  }
  return 0;
}

// Allocate page tables and physical memory to grow process from oldsz to
// newsz, which need not be page aligned.  Returns new size or 0 on error.
int
allocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  char *mem;
  uint a;

  if(newsz >= KERNBASE)
    return 0;
  if(newsz < oldsz)
    return oldsz;

  a = PGROUNDUP(oldsz);
  for(; a < newsz; a += PGSIZE){
    mem = kalloc();
    myproc()->rss+=PGSIZE;
    if(mem == 0){
      cprintf("allocuvm out of memory\n");
      deallocuvm(pgdir, newsz, oldsz);
      return 0;
    }
    memset(mem, 0, PGSIZE);
    if(mappages(pgdir, (char*)a, PGSIZE, V2P(mem), PTE_W|PTE_U) < 0){
      cprintf("allocuvm out of memory (2)\n");
      deallocuvm(pgdir, newsz, oldsz);
      kfree(mem);
      return 0;
    }
    pte_t* pte=walkpgdir(pgdir,(char*)a,0);
    incre_rev_map(V2P(mem),pte);
    cprintf("alloc %d %d %d %d\n",V2P(mem),myproc()->pid, (*pte & PTE_W),PTE_ADDR(*pte));
    cprintf("ref error %d %d\n", rev_map[V2P(mem)/PGSIZE].pg_ref_count, pte);
  }
  return newsz;
}

// Deallocate user pages to bring the process size from oldsz to
// newsz.  oldsz and newsz need not be page-aligned, nor does newsz
// need to be less than oldsz.  oldsz can be larger than the actual
// process size.  Returns the new process size.
int
deallocuvm(pde_t *pgdir, uint oldsz, uint newsz)
{
  pte_t *pte;
  uint a, pa;

  if(newsz >= oldsz)
    return oldsz;

  a = PGROUNDUP(newsz);
  for(; a  < oldsz; a += PGSIZE){
    pte = walkpgdir(pgdir, (char*)a, 0);
    if(!pte)
      a = PGADDR(PDX(a) + 1, 0, 0) - PGSIZE;
    else if((*pte & PTE_P) != 0){
      pa = PTE_ADDR(*pte);
      if(pa == 0)
        panic("kfree");
      // char *v = P2V(pa);
      // kfree(v);
      decre_rev_map(pa,pte); // also handle case when this page in swapped block
      *pte = 0;
      if (myproc()->rss>0){
        myproc()->rss-=PGSIZE;
      }
    }
  }
  return newsz;
}

// Free a page table and all the physical memory pages
// in the user part.
void
freevm(pde_t *pgdir)
{
  uint i;

  if(pgdir == 0)
    panic("freevm: no pgdir");
  deallocuvm(pgdir, KERNBASE, 0);
  for(i = 0; i < NPDENTRIES; i++){
    if(pgdir[i] & PTE_P){
      char * v = P2V(PTE_ADDR(pgdir[i]));
      kfree(v);
    }
  }
  kfree((char*)pgdir);
}

// Clear PTE_U on a page. Used to create an inaccessible
// page beneath the user stack.
void
clearpteu(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  if(pte == 0)
    panic("clearpteu");
  *pte &= ~PTE_U;
}

// Given a parent process's page table, create a copy
// of it for a child.
pde_t*
copyuvm(pde_t *pgdir, uint sz,struct proc* child)
{
  pde_t *d;
  pte_t *pte;
  uint pa, i, flags;
  // char *mem;
  // cprintf("IN COPYUVM\n");
  if((d = setupkvm()) == 0)
    return 0;
  for(i = 0; i < sz; i += PGSIZE){
    if((pte = walkpgdir(pgdir, (void *) i, 0)) == 0)
      panic("copyuvm: pte should exist");
    if(!(*pte & PTE_P))
      panic("copyuvm: page not present");
    
    // *pte &=~PTE_W;
    pa = PTE_ADDR(*pte);
    flags = PTE_FLAGS(*pte);
    flags &=~PTE_W;
    // if((mem = kalloc()) == 0)
    //   goto bad;

    if(mappages(d, (void*)i, PGSIZE, pa, flags) != 0) {
      // kfree(mem);
      goto bad;
    }
    child->rss+=PGSIZE;
    *pte &=~PTE_W;
    pte_t* new_pte=walkpgdir(d,(void*)i,0);
    incre_rev_map(pa,new_pte);
    cprintf("copyuvm %d %d\n",pa, myproc()->pid);
    // cprintf("no. of reference %d\n",rev_map[pa/PGSIZE].pg_ref_count);
    // cprintf("NEW PTE AND OLD PTE %d %d\n",*pte, *new_pte);
  }
  lcr3(V2P(pgdir));
  return d;

bad:
  freevm(d);
  return 0;
}

//PAGEBREAK!
// Map user virtual address to kernel address.
char*
uva2ka(pde_t *pgdir, char *uva)
{
  pte_t *pte;

  pte = walkpgdir(pgdir, uva, 0);
  if((*pte & PTE_P) == 0)
    return 0;
  if((*pte & PTE_U) == 0)
    return 0;
  return (char*)P2V(PTE_ADDR(*pte));
}

// Copy len bytes from p to user address va in page table pgdir.
// Most useful when pgdir is not the current page table.
// uva2ka ensures this only works for PTE_U pages.
int
copyout(pde_t *pgdir, uint va, void *p, uint len)
{
  char *buf, *pa0;
  uint n, va0;

  buf = (char*)p;
  while(len > 0){
    va0 = (uint)PGROUNDDOWN(va);
    pa0 = uva2ka(pgdir, (char*)va0);
    if(pa0 == 0)
      return -1;
    n = PGSIZE - (va - va0);
    if(n > len)
      n = len;
    memmove(pa0 + (va - va0), buf, n);
    len -= n;
    buf += n;
    va = va0 + PGSIZE;
  }
  return 0;
}

//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.
//PAGEBREAK!
// Blank page.

void update_pte(uint pa, uint store_permission, pte_t* pte){
  for(int i=0; i<NPROC; i++){
    if (rev_map[pa/PGSIZE].fill[i]==-1){
      rev_map[pa/PGSIZE].fill[i]=1;
      rev_map[pa/PGSIZE].pg_ref_count+=1;
      *pte=pa|store_permission|PTE_A;
      rev_map[pa/PGSIZE].pid_arr[i]=pte;
      return;
    }
  }
}

void null_rev_map(uint pa){
  // acquire(&rev_map[pa/PGSIZE].lock);
  for(int i=0; i<NPROC; i++){
    if (rev_map[pa/PGSIZE].fill[i]!=-1){
      cprintf("Null %d %d %d\n",rev_map[pa/PGSIZE].pid_arr[i],*rev_map[pa/PGSIZE].pid_arr[i],PTE_ADDR(*rev_map[pa/PGSIZE].pid_arr[i]));
    }
    rev_map[pa/PGSIZE].fill[i]=-1;
  }
  rev_map[pa/PGSIZE].pg_ref_count=0;
  // release(&rev_map[pa/PGSIZE].lock);
  return;
}

void tenpercent(pde_t* p,uint sz){
  int count=0;
  for(int i=0; i<sz; i+=PGSIZE){
    pte_t* pte=walkpgdir(p,(void*)i,0);
    if ((*pte & PTE_A) && (*pte & PTE_P)){
      count+=1;
    }
  }
  int num_free=(count+9)/10;
  uint va=0;
  while(num_free && va<=sz){
    pte_t* pte= walkpgdir(p, (void*)va,0);
      if ((*pte & PTE_P) && (*pte & PTE_A)){
          *pte &= ~PTE_A;
          num_free--;
      }
      va+=PGSIZE;
  }
  return;
}

pte_t* select_a_victim(pde_t* pgdir,uint sz){
  for(int i=0; i<sz; i+=PGSIZE){
      pte_t* pte=walkpgdir(pgdir, (void*)i, 0);
      if ((*pte & PTE_P) && (!(*pte & PTE_A))){
        return pte;
      }
  }
  return 0; // remember to check that *pte=0 holds or not
}

// int swap_page_from_pte(pte_t* pte){
//   for(int i=0; i<NSLOTS; i++){
//     if (sblocks[i].is_free){
//       char *mem=(char*)P2V(PTE_ADDR(*pte));
//       write_swap_page(ROOTDEV,mem,8*i+2);
//       sblocks[i].is_free=0;
//       sblocks[i].page_perm=PTE_FLAGS(*pte);
//       *pte=i<<12|PTE_S;
//       kfree(mem);
//       return i;
//     }
//   }
// }

void swap_page(){
  cprintf("in swap_page\n");
  struct proc *p = victim_proc();
  cprintf("victim process %d %d %d\n",p->pid,p->state,p->rss);
  pte_t* pte=select_a_victim(p->pgdir,p->sz);
  if (pte==0){
    cprintf("in tenpercent\n");
    tenpercent(p->pgdir,p->sz);
    pte=select_a_victim(p->pgdir,p->sz);
    cprintf("after tenpercent\n");
  }
  if (pte==0){
    panic("page not found again\n");
  }
  // update rss of all process sharing the page
  uint pa=PTE_ADDR(*pte);
  cprintf("victim physical page %d\n",pa);
  int blockid=-1;
  for(int i=0; i<NSLOTS; i++){
    if (sblocks[i].is_free){
      char *mem=(char*)P2V(PTE_ADDR(*pte));
      write_swap_page(ROOTDEV,mem,8*i+2);
      sblocks[i].is_free=0;
      for(int j=0; j<NPROC; j++){
        if (sblocks[i].fill[j]){
          sblocks[i].fill[j]=0;
          sblocks[i].page_perm[j]=PTE_FLAGS(*pte);
          sblocks[i].arr[j]=p->pid;
          *pte=i<<12|PTE_S;
          sblocks[i].pte_entry[j]=pte;
          blockid=i;
          cprintf("checking %d %d\n",(*sblocks[i].pte_entry[j] & PTE_S),(*sblocks[i].pte_entry[j]));
          kfree(mem);
          break;
        }
      }
      cprintf("checking %d %d\n",(*pte & PTE_S),*pte);
      break;
    }
  }

  // for(int i=0; i<NPROC; i++){
  //   if (rev_map[pa/PGSIZE].fill[i]!=-1){
  //     cprintf("%d ",i);
  //   }
  // }
  // cprintf("\n");
  cprintf("ref count in swap %d\n",rev_map[pa/PGSIZE].pg_ref_count);
  cprintf("blockid %d \n",blockid);

  // make refcount equal to zero.
  null_rev_map(pa);

  int found=0;
  for(int i=0; i<NPROC; i++){
    // cprintf("iteration going on %d\n",i);
    int pid=getpid(i);
    if (pid==-1){continue;}
    pde_t* pde=getpagedir(pid);
    // cprintf("iteration going on %d\n",i);
    if (pid==p->pid){decrement_rss(pid); continue;}
    // cprintf("iteration going on %d\n",i);
    for(int j=0; j<NPDENTRIES; j++){
      if (pde[j] & PTE_P){
        pte_t* ans=(pte_t*)P2V(PTE_ADDR(pde[j]));
        for(int m=0; m<NPTENTRIES; m++){
          if (PTE_ADDR(ans[m])==pa && (ans[m] & PTE_P) && (ans[m] & PTE_A)){
              pte_t* che=&((ans[m])); // why is it needed to convert it into virtual
              cprintf("victim friend physical page %d %d %d %d %d \n",PTE_ADDR(ans[m]), pid, che, PTE_ADDR(*che),*che);
              for(int k=0; k<NPROC; k++){
                if (sblocks[blockid].fill[k]){
                  cprintf("found %d\n",pid);
                  sblocks[blockid].fill[k]=0;
                  sblocks[blockid].page_perm[k]=PTE_FLAGS(*che);
                  sblocks[blockid].arr[k]=pid;
                  *che=blockid<<12|PTE_S;
                  sblocks[blockid].pte_entry[k]=che;
                  break;
                }
              }
              found=1;
              break;
          }
        }
        if (found==1){
          decrement_rss(pid);
          // cprintf("aage badho\n");
          found=0;
          break;
        }
      }
    }
  }
  // cprintf("returning from swap page\n");
  return;
}

// when we free_page we also have to null rev_map
void free_page(pde_t* pde){
  for(int i=0; i<NPDENTRIES; i++){
    if (pde[i] & PTE_P){
      pte_t* ans=(pte_t*)P2V(PTE_ADDR(pde[i]));
      for(int j=0; j<NPTENTRIES; j++){
        if (ans[j] & PTE_S){
          sblocks[PTE_ADDR(ans[j])>>12].is_free=1;
        }
      }
    }
  }
  return;
}




void handle_pgfault(){
  uint va=rcr2();
  pte_t* pte;
  struct proc *p=myproc();
  pte=walkpgdir(p->pgdir,(void*)va,0);
  cprintf("in pagefault %d %d %d %d\n",p->pid , (*pte & PTE_S), (*pte & PTE_W), p->killed);
  if (*pte & PTE_S){
    cprintf("Swapped\n");
    int blockid= (*pte)>>12;
    char* mem=kalloc();
    mem=read_swap_page(mem,2+8*blockid);
    sblocks[blockid].is_free=1;
    // *pte=PTE_ADDR(V2P(mem))|PTE_FLAGS(store_permission);
    // *pte=*pte|PTE_A;
    // update rss of all process having this physical page;
    uint pa=PTE_ADDR(V2P(mem));
    for(int i=0; i<NPROC; i++){
      if (sblocks[blockid].fill[i]==0){
        increment_rss(sblocks[blockid].arr[i]);
        uint store_permission=sblocks[blockid].page_perm[i];
        update_pte(pa,store_permission,sblocks[blockid].pte_entry[i]);
        sblocks[blockid].fill[i]=1;
      }
    }
    lcr3(V2P(p->pgdir));
  }
  else{
      uint pa=PTE_ADDR(*pte);
      acquire(&rev_map[pa/PGSIZE].lock);
      uint refcount=rev_map[pa/PGSIZE].pg_ref_count;
      release(&rev_map[pa/PGSIZE].lock);
      cprintf("refcount: %d and physical %d\n",refcount, pa);
      if (*pte & ~PTE_U){
        cprintf("hello god\n");
      }

      if (*pte & PTE_W){
        panic("alreday writeable");
      }

      if (refcount>1){
        char *mem;
        if ((mem=kalloc())==0){
          cprintf("Page fault out of memory, kill proc %s with pid %d\n", p->name, p->pid);
          p->killed = 1;
          return;
        }
        memmove(mem,(char*)P2V(pa),PGSIZE);
        // decrement ref_count and entry corresponding to this.
        decre_rev_map(pa,pte);
        uint flags;
        flags=PTE_FLAGS(*pte);
        flags|=PTE_W;
        *pte=V2P(mem)|flags;
        incre_rev_map(V2P(mem),pte);
        cprintf("fault %d %d\n",V2P(mem), pa);
      }
      else if (refcount==1){
        *pte |= PTE_W;
      }
      else{
        panic("some error\n");
      }
      lcr3(V2P(p->pgdir));
  }
  cprintf("returning from pagefalut\n");
  return;
}



