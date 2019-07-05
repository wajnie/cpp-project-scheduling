/* wersja dla project schedulingu - nie ma maszyn, jest m zasobow
   dyskretnych dostepnych w pewnych liczbach jednostek,
   wersja dla roznych alfa (1 lub 2) i ograniczen kolejnosciowych,
   rozwiazaniem jest n n-tek, w ktorych moze wystapic zadanie puste - 0,
   generacja sasiadow na dwa sposoby: standardowe i zamiana dwoch zadan
   z sasiednich kombinacji, z ktorych kazde wystepuje tylko raz,
   metoda REM rozbudowana o przejscia bedace zamiana; zamiana opisywana
   jest przez pare przejsc standardowych,
   restarty - funkcja random_sol,
   funkcja makespan wywoluje solver nieliniowy,
   slajsy i pozycje w slajsach numerowane sa od 0, zadania i zasoby od 1
   parametry podawane w linii polecen (w Borlandzie opcja Run/Arguments) */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <values.h>
#include "cfsqpusr.h"

typedef unsigned   int word;
const word    maxiter=1000;   /* maksymalna liczba iteracji bez poprawy */
const word    maxalfa=2;    /* maksymalny wspolczynnik alfa */
const word    maxx=100;     /* maksymalny stan koncowy zadania */
const word    maxn=50;      /* maksymalna liczba zadan */
const word    maxm=3;       /* maksymalna liczba zasobow dyskretnych */

typedef unsigned   int word;
typedef word       vector[maxn+1];   /* tablica liczb naturalnych */
typedef word       matrix[maxn][maxn]; /* tablica dwuwymiarowa liczb naturalnych */
typedef matrix     solution; /* sekwencja dopuszczalna - n slajsow po n zadan */
typedef word       move[3];       /* przejscie */
typedef word       range[2];      /* uporzadkowana dwojka liczb naturalnych */
struct  rcs_elem   { rcs_elem *prev; move elem; rcs_elem *next; };
                                  /* element RCS-u: przejscie i wskazniki */
typedef rcs_elem   *rcs_pointer;
enum    boolean    { FAL=0, TRU=1 };

solution      bestsol,         /* najlepsze znalezione dotad rozwiazanie */
              currsol,         /* rozwiazanie biezace */
              solvsol;         /* rozwiazanie dla solwera */
word          constraints[maxn+1][maxn+1], /* tablica ogr. kolejnosciowych */
              demands[maxn+1][maxm+1], /* tablica wymagan zasobowych dla zadan */
              resources[maxm+1], /* tablica liczb jednostek zas.dyskretnych */
              utilization[maxn][maxm+1]; /* tablica zuzycia zas.dyskretnych
                                          w slajsach rozwiazania currsol */
rcs_pointer   *rcs_index;      /* tablica wskaznikow do RCS-ow */
word          *rcs_card;       /* tablica licznosci RCS-ow */
word          max_list_length, /* maksymalna liczba RCS-ow */
              finst,           /* numer pierwszej instancji */
              linst,           /* numer ostatniej instancji */
              nbinst,          /* numer biezacej instancji */
              nbiter,          /* numer biezacej iteracji */
              bestiter,        /* numer iteracji z najlepszym rozwiazaniem */
              maxsol,          /* maksymalna liczba sprawdzanych rozwiazan */
              nbsol,           /* liczba dotad sprawdzonych rozwiazan */
              nbbestsol,       /* numer najlepszego dotad rozwiazania */
              which_rcs,       /* numer RCS-u do usuniecia z listy */
              noe,             /* liczba krawedzi w grafie ogr.kol. */
              hmr,             /* liczba restartow */
              n,m;             /* liczba zadan i maszyn */
vector        x_table,         /* tablica stanow koncowych zadan */
              alfa;            /* tablica wspolczynnikow alfa zadan */
range         job_range[maxn+1]; /* tablica dwojek oznaczajacych poczatkowa
                                  i koncowa kombinacje zadania */
double 	      m_bestsol,       /* funkcja celu najlepszego rozwiazania */
              m_currsol;       /* funkcja celu biezacego rozwiazania */
float         q,               /* zadana gestosc grafu ogr.kol. */
              qr;              /* rzeczywista gestosc grafu */
boolean       list_is_full;    /* czy lista jest pelna */
clock_t       tstart,tstop;    /* zmienne do zliczania czasu */
FILE          *resfile1,        /* plik z wynikami */
              *resfile2;        /* plik z informacjami */
char          *filename1 [15],   /* nazwa pliku z wynikami */
              *filename2 [15];   /* nazwa pliku z informacjami */

word generator (word range) {
   return rand() % range; }

double trunc (double arg, word exact) {
   return floor(arg*pow(10,exact))/pow(10,exact); }

void disp_sol (solution s) {
word i,j;
   for (i=0; i<n; i++) {
      printf("(");
      j=0;
      while (s[i][j]!=0) {
         printf("%u ",s[i][j]);
         j++; }
      printf(")"); }
   printf("\n"); }

void write_sol (solution s) {
word i,j;
   for (i=0; i<n; i++) {
      fprintf(resfile2,"(");
      j=0;
      while (s[i][j]!=0) {
         fprintf(resfile2,"%u ",s[i][j]);
         j++; }
      fprintf(resfile2,")"); } }

void copy_sol (solution s1, solution s2) {
word i,j;
   for (i=0; i<n; i++)
   for (j=0; j<n; j++)
      s2[i][j]=s1[i][j]; }

/*------------------METODA REM---------------------*/

word choose_rcs (void) {
word max,which,i;
   max=rcs_card[0];
   which=0;
   for (i=1; i<max_list_length; i++)
      if (rcs_card[i]>max) {
         max=rcs_card[i];
         which=i; }
   return which; }

boolean comp_moves (move e1, move e2) {
boolean equal;
word i;
   equal=TRU;
   i=0;
   while (equal && i<3) {
      equal=(boolean)(equal && e1[i]==e2[i]);
      i++; }
   return equal; }

void copy_move (move e1, move e2) {
word i;
   for (i=0; i<3; i++)
      e2[i]=e1[i]; }

void reverse_move (move e1, move e2) {
   e2[0]=e1[0];
   e2[1]=e1[2];
   e2[2]=e1[1]; }

boolean try_shorten (move e1, move e2) {
   if (e1[0]==e2[0]) {
      if (e1[2]==e2[1]) {
         e1[2]=e2[2];
         return TRU; }
      else
         if (e1[1]==e2[2]) {
            e1[1]=e2[1];
            return TRU; }
         else
            return FAL; }
   else
      return FAL; }

void clean_rcs (word l) {
rcs_pointer p,q;
   p=rcs_index[l];
   while (p!=NULL) {
      q=(*p).next;
      delete p;
      p=q; }
   rcs_index[l]=NULL;
   rcs_card[l]=0; }

rcs_pointer where_on_rcs (word l, move e) {
rcs_pointer p;
boolean is;
   is=FAL;
   p=rcs_index[l];
   while (p!=NULL && !is) {
      is=comp_moves((*p).elem,e);
      if (!is)
         p=(*p).next; }
   if (is)
      return p;
   else
      return NULL; }

void out_of_rcs (word l, rcs_pointer addr) {
rcs_pointer p,q;
   p=(*addr).prev;
   q=(*addr).next;
   if (p!=NULL)
      (*p).next=q;
   else
      rcs_index[l]=q;
   if (q!=NULL)
      (*q).prev=p;
   delete addr;
   rcs_card[l]--; }

void onto_rcs (word l, move e) {
rcs_pointer p,q,r;
boolean shorty,first,second;
move tmp;
   if (rcs_index[l]==NULL) {
      rcs_index[l]=new rcs_elem;
      (*rcs_index[l]).prev=(*rcs_index[l]).next=NULL;
      copy_move(e,(*rcs_index[l]).elem);
      rcs_card[l]++; }
   else {
      copy_move(e,tmp);
      p=rcs_index[l];
      first=second=FAL;
      while (p!=NULL && !second) {
         shorty=try_shorten((*p).elem,tmp);
         if (shorty) {
            if (!first) {
               copy_move((*p).elem,tmp);
               r=p;
               first=TRU; }
            else
               second=TRU; }
         else {
            q=p;
            p=(*p).next; } }
      if (second)
         out_of_rcs(l,r);
      if (!first) {
         p=new rcs_elem;
         copy_move(e,(*p).elem);
         (*p).prev=q;
         (*p).next=NULL;
         (*q).next=p;
         rcs_card[l]++; } } }

void modify_list (move e, boolean ex) {
rcs_pointer place;
move erev,e1,erev1;
word i;
   if (!ex) {
      reverse_move(e,erev);
      for (i=0; i<max_list_length; i++)
         if (rcs_card[i]>0)
            if (rcs_card[i]==1)
               onto_rcs(i,erev);
            else {
               place=where_on_rcs(i,e);
               if (place==NULL)
                  onto_rcs(i,erev);
               else
                  out_of_rcs(i,place); }
      if (!list_is_full) {
         onto_rcs(which_rcs,erev);
         which_rcs++;
         if (which_rcs>=max_list_length)
            list_is_full=TRU; }
      else {
         which_rcs=choose_rcs();
         clean_rcs(which_rcs);
         onto_rcs(which_rcs,erev); } }
   else {
      e1[0]=e[0]+1;
      e1[1]=e[2];
      e1[2]=e[1];
      reverse_move(e,erev);
      reverse_move(e1,erev1);
      for (i=0; i<max_list_length; i++)
         if (rcs_card[i]>0)
            if (rcs_card[i]==1) {
               onto_rcs(i,erev);
               onto_rcs(i,erev1); }
            else {
               place=where_on_rcs(i,e);
               if (place==NULL)
                  onto_rcs(i,erev);
               else
                  out_of_rcs(i,place);
               place=where_on_rcs(i,e1);
               if (place==NULL)
                  onto_rcs(i,erev1);
               else
                  out_of_rcs(i,place); }
      if (!list_is_full) {
         onto_rcs(which_rcs,erev);
         onto_rcs(which_rcs,erev1);
         which_rcs++;
         if (which_rcs>=max_list_length)
            list_is_full=TRU; }
      else {
         which_rcs=choose_rcs();
         clean_rcs(which_rcs);
         onto_rcs(which_rcs,erev);
         onto_rcs(which_rcs,erev1); } } }

void modify_tables (move e, boolean ex) {
word j,tmp;
   if (!ex) {
      if (e[0]==job_range[e[1]][0])
         job_range[e[1]][0]++;
      else
         job_range[e[1]][1]--;
      if (e[0]==job_range[e[2]][1]+1)
        job_range[e[2]][1]++;
      else
        job_range[e[2]][0]--;
      for (j=1; j<m+1; j++)
         utilization[e[0]][j]+=(demands[e[2]][j]-demands[e[1]][j]); }
  else {
     tmp=job_range[e[1]][0];
     job_range[e[1]][0]=job_range[e[1]][1]=job_range[e[2]][0];
     job_range[e[2]][0]=job_range[e[2]][1]=tmp;
      for (j=1; j<m+1; j++) {
         utilization[e[0]][j]+=(demands[e[2]][j]-demands[e[1]][j]);
         utilization[e[0]+1][j]+=(demands[e[1]][j]-demands[e[2]][j]); } } }

boolean is_tabu (move e) {
boolean is;
word i;
   is=FAL;
   i=0;
   while (i<max_list_length && !is) {
      if (rcs_card[i]==1) {
         is=comp_moves((*rcs_index[i]).elem,e);
         if (!is)
            i++; }
      else
         i++; }
   return is; }

boolean is_tabu_ex (move e) {
move e1,elem1,elem2;
boolean is;
word i;
   e1[0]=e[0]+1;
   e1[1]=e[2];
   e1[2]=e[1];
   is=FAL;
   i=0;
   while (i<max_list_length && !is) {
      if (rcs_card[i]==2) {
         copy_move((*rcs_index[i]).elem,elem1);
         copy_move((*(*rcs_index[i]).next).elem,elem2);
         is=(boolean)((comp_moves(elem1,e) && comp_moves(elem2,e1)) ||
                      (comp_moves(elem1,e1) && comp_moves(elem2,e)));
         if (!is)
            i++; }
      else
         i++; }
   return is; }

/*--------------------------KONIEC REM---------------------*/

void obj32 (int nparam, int j, double* x, double* fj, void* cd) {
int i,k;
double b,c_2;
   *fj=0.0;
   for (i=0; i<n; i++) {
      b=c_2=0.0;
      for (k=0; k<n; k++)
        if (alfa[solvsol[i][k]]==1)
           b+=x[i*n+k];
        else
           c_2+=x[i*n+k]*x[i*n+k];
      *fj+=b+sqrt(b*b+4*c_2); }
   *fj=*fj/2.0; }

void cntr32 (int nparam, int j, double* x, double* gj, void *cd) {
int i,k;
   *gj=x_table[j-1];
   for (i=0; i<n; i++)
   for (k=0; k<n; k++)
      if (solvsol[i][k]==j-1)
         *gj-=x[i*n+k]; }

double solver (void) {
   int nparam,nf,nineq,neq,mode,iprint,miter,neqn,nineqn,
       ncsrl,ncsrn,nfsr,mesh_pts[1],inform,i,k;
   double bigbnd,eps,epsneq,udelta,result;
   double *x,*bl,*bu,*f,*g,*lambda;
   void *cd;

                        /* wybor algorytmu ! */
   mode=100;
                        /* opcje wyprowadzania wynikow */
   iprint=0;
                        /* maksymalna dopuszczalna liczba iteracji */
   miter=1000;
                        /* pelni role nieskonczonosci */
   bigbnd=1.e10;
                   /* jakas norma - musi byc wieksza od precyzji maszyny */
   eps=1.e-3;
             /* maksymalne naruszenie ograniczen rownosciowych nieliniowych */
   epsneq=1.e-1;
                        /* rozmiar perturbacji (?)- najlepiej zeby bylo 0.0 */
   udelta=0.e0;
                        /* liczba zmiennych swobodnych */
   nparam=n*n;
                        /* liczba funkcji celu */
   nf=1;
                        /* liczba ograniczen rownosciowych nieliniowych */
   neqn=0;
                        /* liczba ograniczen nierownosciowych nieliniowych */
   nineqn=0;
                        /* calkowita liczba ograniczen nierownosciowych */
   nineq=0;
                        /* calkowita liczba ograniczen rownosciowych */
   neq=n+1;
                        /* dotyczy ograniczen zwiazanych (?)*/
   ncsrl=ncsrn=nfsr=mesh_pts[0]=0;
                        /* tablica dolnych ograniczen */
   bl=(double*)calloc(nparam,sizeof(double));
                        /* tablica gornych ograniczen */
   bu=(double*)calloc(nparam,sizeof(double));
                        /* tablica zmiennych swobodnych */
   x=(double*)calloc(nparam,sizeof(double));
                        /* tablica wartosci funkcji celu */
   f=(double*)calloc(nf+1,sizeof(double));
                        /* tablica ograniczen */
   g=(double*)calloc(nineq+neq+1,sizeof(double));
   lambda=(double*)calloc(nineq+neq+nf+nparam,sizeof(double));

/* ustalenie dolnych bl, gornych bu ograniczen i rozwiazan startowych x */
   for (i=0; i<n*n; i++) {
      bl[i]=0.0;
      bu[i]=double(maxx);
      x[i]=0.0; }

   for (i=1; i<n+1; i++) {
      for (k=0; solvsol[k/n][k%n]!=i; k++);
      x[k]=x_table[i]; }

   cfsqp(nparam,nf,nfsr,nineqn,nineq,neqn,neq,ncsrl,ncsrn,mesh_pts,
         mode,iprint,miter,&inform,bigbnd,eps,epsneq,udelta,bl,bu,x,f,g,
         lambda,obj32,cntr32,grobfd,grcnfd,cd);

   free(bl);
   free(bu);
   free(x);
   result=f[0];
   free(f);
   free(g);
   free(lambda);
   return result; }

double makespan (solution s) {
   copy_sol(s,solvsol);
   nbsol++;
   return trunc(solver(),4); }
//   return (double)generator(500); }

word replacable(solution s, word k, word l, boolean &first) {
word mbeg,mend;
   if (first) {
      if (s[k][l]==0) {
         first=FAL;
         return 1; }
      else {
         mbeg=job_range[s[k][l]][0];
         mend=job_range[s[k][l]][1];
         if (k>mbeg && k<mend)
            return 0;
         else
            if (mbeg==mend)
               return 2;
            else
               return 1; } }
   else
      return 0; }

boolean is_there(word z, solution s, word l) {
boolean is;
word i;
   is=FAL;
   i=0;
   while (i<n && !is) {
      if (s[l][i]==z)
         is=TRU;
      else
         i++; }
   return is; }

boolean is_successor(word z, solution s, word l, word k) {
boolean is;
word i;
   if (constraints[z][0]==0)
      return FAL;
   else {
      is=FAL;
      i=0;
      while (i<n && !is) {
         if (constraints[z][s[l][i]]==1 && i!=k)
            is=TRU;
         else
            i++; }
      return is; } }

boolean is_predecessor(word z, solution s, word l, word k) {
boolean is;
word i;
   if (constraints[0][z]==0)
      return FAL;
   else {
      is=FAL;
      i=0;
      while (i<n && !is) {
         if (constraints[s[l][i]][z]==1 && i!=k)
            is=TRU;
         else
            i++; }
      return is; } }

boolean res_violiation(word z, solution s, word l, word k) {
boolean viol;
word j;
   viol=FAL;
   j=1;
   while (j<m+1 && !viol) {
      if (utilization[l][j]+demands[z][j]-demands[s[l][k]][j] > resources[j])
         viol=TRU;
      else
         j++; }
   return viol; }

void set_start_sol (solution s) {
word i,j;
      for (i=0; i<n; i++)
      for (j=0; j<n; j++)
         if (j==0)
            s[i][j]=i+1;
         else
            s[i][j]=0;
      for (i=1; i<n+1; i++)
         job_range[i][0]=job_range[i][1]=i-1;
      for (i=0; i<n; i++)
      for (j=1; j<m+1; j++)
         utilization[i][j]=demands[i+1][j]; }

void random_sol (solution s) {
word candidates[maxn],job,ind,pos,i,j,k,l;
   for (i=0; i<n; i++)
   for (j=0; j<n; j++)
      s[i][j]=0;
   k=0;
   for (i=0; i<n; i++) {
      ind=0;
      for (j=1; j<n+1; j++)
         if (constraints[0][j]==i) {
            candidates[ind]=j;
            ind++; }
      while (ind>0) {
         pos=generator(ind);
         job=candidates[pos];
         s[k][0]=job;
         job_range[job][0]=job_range[job][1]=k;
         for (l=1; l<m+1; l++)
            utilization[k][l]=demands[job][l];
         candidates[pos]=candidates[ind-1];
         ind--;
         k++; } } }

void restart (solution s, double &m_s) {
word i;
   random_sol(s);
   m_s=makespan(s);
   if (m_s < m_bestsol) {
      copy_sol(s,bestsol);
      m_bestsol=m_s; }
   bestiter=nbiter;
   for (i=0; i<max_list_length; i++)
      clean_rcs(i);
   which_rcs=0;
   list_is_full=FAL;
   hmr++; }

void iteration (solution s, double &m_s) {
solution neigh,bestneigh;
move mv,bestmove;
const double very_big_num=MAXDOUBLE;
double m_bestneigh,m_neigh;
word cand,state,i,j,k;
boolean first_zero,exchange;
   m_bestneigh=very_big_num;
   i=j=0;
   first_zero=TRU;
   exchange=FAL;
   while (i<n) {
      state=replacable(s,i,j,first_zero);
      if (state!=0)
         if (state==1) /* mozna zastepowac */ {
            if (i>0) {
               k=0;
               while (s[i-1][k]!=0) {
                  cand=s[i-1][k];
                  if (!is_there(cand,s,i) &&
                      !is_successor(cand,s,i,j) &&
                      !res_violiation(cand,s,i,j)) {
                     mv[0]=i;
                     mv[1]=s[i][j];
                     mv[2]=cand;
                     if (!is_tabu(mv)) {
                        copy_sol(s,neigh);
                        neigh[i][j]=cand;
//                        disp_sol(neigh);
                        m_neigh=makespan(neigh);
                        if (m_neigh < m_bestneigh) {
                           copy_sol(neigh,bestneigh);
                           m_bestneigh=m_neigh;
                           copy_move(mv,bestmove);
                           exchange=FAL; } } }
                  k++; } }
            if (i<n-1) {
               k=0;
               while (s[i+1][k]!=0) {
                  cand=s[i+1][k];
                  if (!is_there(cand,s,i) &&
                      !is_predecessor(cand,s,i,j) &&
                      !res_violiation(cand,s,i,j)) {
                     mv[0]=i;
                     mv[1]=s[i][j];
                     mv[2]=cand;
                     if (!is_tabu(mv)) {
                        copy_sol(s,neigh);
                        neigh[i][j]=cand;
//                        disp_sol(neigh);
                        m_neigh=makespan(neigh);
                        if (m_neigh < m_bestneigh) {
                           copy_sol(neigh,bestneigh);
                           m_bestneigh=m_neigh;
                           copy_move(mv,bestmove);
                           exchange=FAL; } } }
               k++; } } }
         else /* mozna zamieniac */
            if (i<n-1) {
               k=0;
               while (s[i+1][k]!=0) {
                  cand=s[i+1][k];
                  if (job_range[cand][0]==job_range[cand][1])
                     if (constraints[s[i][j]][cand]==0 &&
                        !is_predecessor(cand,s,i,j) &&
                        !is_successor(s[i][j],s,i+1,k) &&
                        !res_violiation(cand,s,i,j) &&
                        !res_violiation(s[i][j],s,i+1,k)) {
                           mv[0]=i;
                           mv[1]=s[i][j];
                           mv[2]=cand;
                           if (!is_tabu_ex(mv)) {
                              copy_sol(s,neigh);
                              neigh[i][j]=cand;
                              neigh[i+1][k]=s[i][j];
//                              disp_sol(neigh);
                              m_neigh=makespan(neigh);
                              if (m_neigh < m_bestneigh) {
                                  copy_sol(neigh,bestneigh);
                                  m_bestneigh=m_neigh;
                                  copy_move(mv,bestmove);
                                  exchange=TRU; } } }
               k++; } }
      j++;
      if (j>=n) {
         j=0;
         i++;
         first_zero=TRU; } }
   if (m_bestneigh < very_big_num) {
      if (m_bestneigh < m_bestsol) {
         copy_sol(bestneigh,bestsol);
         m_bestsol=m_bestneigh;
         bestiter=nbiter;
         nbbestsol=nbsol; }
      copy_sol(bestneigh,s);
      m_s=m_bestneigh;
      modify_list(bestmove,exchange);
      modify_tables(bestmove,exchange); }
   else
      restart(s,m_s); }

void parameters (int hmpar, char *par[]) {
word i,k;
   k=1;
   n=(word)atoi(par[k]);
   k++;
   m=(word)atoi(par[k]);
   k++;
   for (i=1; i<m+1; i++)
      resources[i]=(word)atoi(par[k+i-1]);
   k+=m;
   q=(float)atof(par[k]);
   k++;
   max_list_length=(word)atoi(par[k]);
   k++;
   rcs_index=(rcs_pointer*)(malloc(max_list_length*sizeof(rcs_pointer)));
   rcs_card=(word*)(malloc(max_list_length*sizeof(word)));
   for (i=0; i<max_list_length; i++) {
      rcs_index[i]=NULL;
      rcs_card[i]=0; }
   maxsol=(word)atoi(par[k]);
   k++;
   (*filename1)=par[k];
   k++;
   (*filename2)=par[k];
   k++;
   finst=(word)atoi(par[k]);
   k++;
   linst=(word)atoi(par[k]); }

void complete_graph (void) {
word i,j,k;
   for (i=1; i<n+1; i++)
   for (j=i+1; j<n+1; j++)
      if (constraints[i][j]==1)
         for (k=j+1; k<n+1; k++)
            if (constraints[j][k]==1)
               if (constraints[i][k]!=1) {
                  constraints[i][k]=1;
                  constraints[i][0]++;
                  constraints[0][k]++;
                  noe++; } }

void random_graph (void) {
word maxnoe,maxnoeq,i,j,k,r;
   maxnoe=n*(n-1)/2;
   noe=0;
   maxnoeq=(word)floor(maxnoe*q);
   while (noe<maxnoeq) {
      r=generator(maxnoe);
      i=1;
      j=i+1;
      k=1;
      while (k<r) {
         j++;
         if (j>n) {
            i++;
            j=i+1; }
         k++; }
      if (constraints[i][j]!=1) {
         constraints[i][j]=1;
         constraints[i][0]++;
         constraints[0][j]++;
         noe++;
         complete_graph(); } }
   qr=(float)noe/maxnoe; }

void initiation (void) {
word i,j;
   for (i=0; i<max_list_length; i++)
      clean_rcs(i);
   which_rcs=0;
   list_is_full=FAL;
   nbiter=bestiter=nbsol=nbbestsol=hmr=0;
   srand(nbinst);
   x_table[0]=0;
   alfa[0]=2;
   for (j=1; j<m+1; j++)
      demands[0][j]=0;
   for (i=1; i<n+1; i++) {
      x_table[i]=generator(maxx)+1;
      alfa[i]=generator(maxalfa)+1;
      for (j=1; j<m+1; j++)
         demands[i][j]=generator((word)ceil(0.5*resources[j])+1); }
   for (i=0; i<n+1; i++)
   for (j=0; j<n+1; j++)
      constraints[i][j]=0;
   random_graph();
   set_start_sol(currsol);
//   disp_sol(currsol);
   m_currsol=makespan(currsol);
//   printf("  %3.3f\n",m_currsol);
   copy_sol(currsol,bestsol);
   m_bestsol=m_currsol; }

void results (void) {
   resfile1=fopen(*filename1,"at");
   resfile2=fopen(*filename2,"at");
   fprintf(resfile1,"%3u) %4.3f\n",nbinst,m_bestsol);
   fprintf(resfile2,"%3u) ",nbinst);
   write_sol(bestsol);
   fprintf(resfile2," %3u %3u %3u %3u %3u %3.2f %1.2f\n",nbbestsol,nbsol,
      bestiter,nbiter,hmr,(tstop-tstart)/1000000.0,qr);
   fclose(resfile1);
   fclose(resfile2); }

void conclusion (void) {
word i;
   for (i=0; i<max_list_length; i++)
      clean_rcs(i);
   free(rcs_index);
   free(rcs_card); }

main(int hmpar, char *par[]) {
   parameters(hmpar,par);
   for (nbinst=finst; nbinst<=linst; nbinst++) {
       initiation();
       tstart=clock();
       while (nbsol<=maxsol) {
          nbiter++;
          if (nbiter-bestiter==maxiter)
             restart(currsol,m_currsol);
          else {
             iteration(currsol,m_currsol); } }
//             disp_sol(currsol);
//             printf("%u %f %u\n",nbiter,m_currsol,bestiter); } }
       tstop=clock();
       results(); }
   conclusion(); }
