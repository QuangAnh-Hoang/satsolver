#include "solver.h"


// Global variables
int learnt[512];
int learntSize = 0;
int reduceMap[64*1024];
int reduceMapSize = 0;
Clause clauseDB[512*1024];
int clauseDBSize = 0;
WL watchedPointers[NumVars*2+1][32*1024];
int watchedPointersSize[NumVars*2+1] = {0,};


// Heap data structure
void heap_initialize( Heap *h, const double *a ) {
	h->activity = a;
	h->heapSize = 0;
	h->posSize = 0;
}

int heap_compare( Heap *h, int a, int b ) {
	if ( h->activity[a] > h->activity[b] ) return 1; 
	else return 0;
}

void heap_up( Heap *h, int v ) {
	int x = h->heap[v];
	int p = Parent(v);
        while ( v && heap_compare(h, x, h->heap[p]) ) {
       		h->heap[v] = h->heap[p];
		h->pos[h->heap[p]] = v;
		v = p; 
		p = Parent(p);
        }
        h->heap[v] = x;
	h->pos[x] = v;
}

void heap_down( Heap *h, int v ) {
	int x = h->heap[v];
        while ( ChildLeft(v) < h->heapSize ){
		int child = (ChildRight(v) < h->heapSize) && heap_compare(h, h->heap[ChildRight(v)], h->heap[ChildLeft(v)]) ? 
			    ChildRight(v) : ChildLeft(v);
		if ( heap_compare(h, x, h->heap[child]) ) break;
		else {
			h->heap[v] = h->heap[child];
			h->pos[h->heap[v]] = v;
			v = child;
		}
        }
        h->heap[v] = x;
	h->pos[x] = v;
}

int heap_empty( Heap *h ) { 
	if ( h->heapSize == 0 ) return 1;
	else return 0;
}

int heap_inHeap( Heap *h, int n ) { 
	if ( (n < h->posSize) && (h->pos[n] >= 0) ) return 1;
	else return 0;	
}

void heap_update( Heap *h, int x ) { heap_up(h, h->pos[x]); }

void heap_insert( Heap *h, int x ) {
	if ( h->posSize < x + 1 ) {
		for ( int i = h->posSize; i < x + 1; i ++ ) h->pos[i] = -1;
		h->posSize = x + 1;
	}
	h->pos[x] = h->heapSize;
	h->heap[h->heapSize] = x;
	h->heapSize++;
	heap_up(h, h->pos[x]); 
}

int heap_pop( Heap *h ) {
	int x = h->heap[0];
        h->heap[0] = h->heap[h->heapSize-1];
	h->pos[h->heap[0]] = 0;
	h->pos[x] = -1;
	h->heap[h->heapSize-1] = -1;
	h->heapSize--;
        if ( h->heapSize > 1 ) heap_down(h, 0);
        return x; 
}


// Clause
void clause_init( Clause *c ) { 
	c->lbd = 0;
	c->literalsSize = 0;
}
	
void clause_resize( Clause *c, int sz ) {
	c->lbd = 0;
	if ( sz == c->literalsSize ) {
		c->literalsSize = sz;
	} else if ( sz > c->literalsSize ) {
		for ( int i = c->literalsSize; i < sz; i ++ ) {
			c->literals[i] = -1;
		}
		c->literalsSize = sz;
	} else {
		for ( int i = c->literalsSize; i < sz; i -- ) {
			c->literals[i] = -1;
		}
		c->literalsSize = sz;
	}
}


// Watched Literals
void wl_init( WL *w ) {
	w->clauseIdx = 0;
	w->blocker = 0;
}

void wl_set( WL *w, int c, int b ) {
	w->clauseIdx = c;
	w->blocker = b;
}


// Parse
char *read_whitespace( char *p ) {
        while ( (*p >= 9 && *p <= 13) || *p == 32 ) ++p;
        return p;
}

char *read_until_new_line( char *p ) {
        while ( *p != '\n' ) {
                if ( *p++ == '\0' ) exit(1);
        }
        return ++p;
}

char *read_int( char *p, int *i ) {
        int sym = 1;
        *i = 0;
        p = read_whitespace(p);
        if ( *p == '-' ) {
                sym = 0;
                ++p;
        }
        while ( *p >= '0' && *p <= '9' ) {
                if ( *p == '\0' ) return p;
                *i = *i * 10 + *p - '0';
                ++p;
        }
        if ( !sym ) *i = -(*i);
        return p;
}


// Solver
int solver_add_clause( Solver *s, int c[], int size ) {
	Clause cls;
	clause_init(&cls);
	clause_resize(&cls, size);
    	clauseDB[clauseDBSize++] = cls;
	int id = clauseDBSize - 1;                                
    	for ( int i = 0; i < size; i++ ) clauseDB[id].literals[i] = c[i];
	WL wl;
	wl_set(&wl, id, c[1]);
    	WatchedPointers(-c[0])[WatchedPointersSize(-c[0])++] = wl;
	wl_set(&wl, id, c[0]);
	WatchedPointers(-c[1])[WatchedPointersSize(-c[1])++] = wl;
	return id;                                                      
}

int solver_parse( Solver *s, char *filename ) {
    	FILE *f_data = fopen(filename, "r");  

    	fseek(f_data, 0, SEEK_END);
    	size_t file_len = ftell(f_data);

	fseek(f_data, 0, SEEK_SET);
	char *data = new char[file_len + 1];
	char *p = data;
	fread(data, sizeof(char), file_len, f_data);
	fclose(f_data);                                             
	data[file_len] = '\0';

	int buffer[3];
	int bufferSize = 0;
	while ( *p != '\0' ) {
        	p = read_whitespace(p);
        	if ( *p == '\0' ) break;
        	if ( *p == 'c' ) p = read_until_new_line(p);
       	 	else if ( *p == 'p' ) { 
            		if ( (*(p + 1) == ' ') && (*(p + 2) == 'c') && 
			     (*(p + 3) == 'n') && (*(p + 4) == 'f') ) {
                		p += 5; 
				p = read_int(p, &s->vars); 
				p = read_int(p, &s->clauses);
                		solver_alloc_memory(s);
            		} 
            		else printf("PARSE ERROR(Unexpected Char)!\n"), exit(2);
        	}
        	else {                                                                             
            		int32_t dimacs_lit;
            		p = read_int(p, &dimacs_lit);
            		if ( dimacs_lit != 0 ) { 
				if ( *p == '\0' ) {
                			printf("c PARSE ERROR(Unexpected EOF)!\n");
					exit(1);
				}
				else buffer[bufferSize++] = dimacs_lit;
			}
			else {                                                       
                		if ( bufferSize == 0 ) return 20;
				else if ( bufferSize == 1 ) {
					if ( Value(buffer[0]) == -1 ) return 20;
					else if ( !Value(buffer[0]) ) solver_assign(s, buffer[0], 0, -1);
				}
                		else solver_add_clause(s, buffer, bufferSize);
				bufferSize = 0;
            		}
        	}
    	}
    	s->origin_clauses = clauseDBSize;
    	return ( solver_propagate(s) == -1 ? 0 : 20 );             
}

void solver_alloc_memory( Solver *s ) {
	s->trailSize = s->decVarInTrailSize = 0;

	s->conflicts = s->decides = s->propagations = s->restarts = s->rephases = s->reduces = 0;
	s->threshold = s->propagated = s->time_stamp = 0;
    	s->fast_lbd_sum = s->lbd_queue_size = s->lbd_queue_pos = s->slow_lbd_sum = 0;
    	s->var_inc = 1, s->rephase_inc = 1e5, s->rephase_limit = 1e5, s->reduce_limit = 8192;

	heap_initialize(&s->vsids, s->activity);
    	for (int i = 1; i <= s->vars; i++) {
        	s->value[i] = s->reason[i] = s->level[i] = s->mark[i] = 0;
		s->local_best[i] = s->activity[i] = s->saved[i] = 0;
		heap_insert(&s->vsids, i);
    	}
}

void solver_assign( Solver *s, int literal, int l, int cref ) {
    	int var = abs(literal);
    	s->value[var]  = literal > 0 ? 1 : -1;
    	s->level[var]  = l;
	s->reason[var] = cref;
	s->trail[s->trailSize++] = literal;
}

int solver_decide( Solver *s ) {      
    	int next = -1;
	while ( next == -1 || Value(next) != 0 ) {
        	if (heap_empty(&s->vsids)) return 10;
        	else next = heap_pop(&s->vsids);
    	}
	s->decVarInTrail[s->decVarInTrailSize++] = s->trailSize;
	if ( s->saved[next] ) next *= s->saved[next];
    	solver_assign(s, next, s->decVarInTrailSize, -1);
    	s->decides++;
	return 0;
}

int solver_propagate( Solver *s ) {
    	while ( s->propagated < s->trailSize ) { 
        	int p = s->trail[s->propagated++];
		int size = WatchedPointersSize(p);
        	int i, j;                     
        	for ( i = j = 0; i < size;  ) {
            		int blocker = WatchedPointers(p)[i].blocker;                       
			if ( Value(blocker) == 1 ) {                
                		WatchedPointers(p)[j++] = WatchedPointers(p)[i++]; 
				continue;
            		}
			int cref = WatchedPointers(p)[i].clauseIdx;
			int falseLiteral = -p;
            		Clause& c = clauseDB[cref];              
            		if ( c.literals[0] == falseLiteral ) {
				c.literals[0] = c.literals[1];
				c.literals[1] = falseLiteral;
			}
			i++;
			int firstWP = c.literals[0];
			WL w;
		       	wl_set(&w, cref, firstWP);
			if ( Value(firstWP) == 1 ) {                   
                		WatchedPointers(p)[j++] = w; 
				continue;
            		}
			int k;
			int sz = c.literalsSize;
            		for ( k = 2; (k < sz) && (Value(c.literals[k]) == -1); k++ ); 
			if ( k < sz ) {                           
                		c.literals[1] = c.literals[k];
				c.literals[k] = falseLiteral;
				WatchedPointers(-c.literals[1])[WatchedPointersSize(-c.literals[1])++] = w;
			} else { 
				WatchedPointers(p)[j++] = w;
                		if ( Value(firstWP) == -1 ) { 
                    			while ( i < size ) WatchedPointers(p)[j++] = WatchedPointers(p)[i++];
					WatchedPointersSize(p) = j;
                    			return cref;
                		} else {
					solver_assign(s, firstWP, s->level[abs(p)], cref);
					s->propagations++;
				}
			}
            	}
		// Shrink
		WatchedPointersSize(p) = j;
    	}
    	return -1;                                       
}

void solver_bump_var( Solver *s, int var, double coeff ) {
    	if ( (s->activity[var] += s->var_inc * coeff) > 1e100 ) {
        	for ( int i = 1; i <= s->vars; i++ ) s->activity[i] *= 1e-100;
        	s->var_inc *= 1e-100;
	}
    	if ( heap_inHeap(&s->vsids, var) ) heap_update(&s->vsids, var);
}

int solver_analyze( Solver *s, int conflict, int &backtrackLevel, int &lbd ) {
    	++s->time_stamp;
    	learntSize = 0;
    	Clause &c = clauseDB[conflict]; 
	int conflictLevel = s->level[abs(c.literals[0])];

    	if ( conflictLevel == 0 ) return 20;
	else {
		learnt[learntSize++] = 0;
		int bump[128];
		int bumpSize = 0;
		int should_visit_ct = 0; 
		int resolve_lit = 0;
		int index = s->trailSize - 1;
		do {
			Clause &c = clauseDB[conflict];
			for ( int i = (resolve_lit == 0 ? 0 : 1); i < c.literalsSize; i++ ) {
				int var = abs(c.literals[i]);
				if ( s->mark[var] != s->time_stamp && s->level[var] > 0 ) {
					solver_bump_var(s, var, 0.5);
					bump[bumpSize++] = var;
					s->mark[var] = s->time_stamp;
					if ( s->level[var] >= conflictLevel ) should_visit_ct++;
					else learnt[learntSize++] = c.literals[i];
				}
			}
			do {
				while ( s->mark[abs(s->trail[index--])] != s->time_stamp );
				resolve_lit = s->trail[index + 1];
			} while ( s->level[abs(resolve_lit)] < conflictLevel );
			
			conflict = s->reason[abs(resolve_lit)];
			s->mark[abs(resolve_lit)] = 0;
			should_visit_ct--;
		} while ( should_visit_ct > 0 );

		learnt[0] = -resolve_lit;
		++s->time_stamp;
		lbd = 0;
		
		for ( int i = 0; i < learntSize; i++ ) {
			int l = s->level[abs(learnt[i])];
			if ( l && s->mark[l] != s->time_stamp ) {
				s->mark[l] = s->time_stamp;
				++lbd;
			}
		}

		if ( s->lbd_queue_size < 50 ) s->lbd_queue_size++;
		else s->fast_lbd_sum -= s->lbd_queue[s->lbd_queue_pos];
		
		s->fast_lbd_sum += lbd;
		s->lbd_queue[s->lbd_queue_pos++] = lbd;
		
		if ( s->lbd_queue_pos == 50 ) s->lbd_queue_pos = 0;
		s->slow_lbd_sum += (lbd > 50 ? 50 : lbd);
			
		if ( learntSize == 1 ) backtrackLevel = 0;
		else {
			int max_id = 1;
			for ( int i = 2; i < learntSize; i++ ) {
				if ( s->level[abs(learnt[i])] > s->level[abs(learnt[max_id])] ) max_id = i;
			}
			int p = learnt[max_id];
			learnt[max_id] = learnt[1];
			learnt[1] = p;
			backtrackLevel = s->level[abs(p)];
		}

		for ( int i = 0; i < bumpSize; i++ ) {   
			if ( s->level[bump[i]] >= backtrackLevel - 1 ) solver_bump_var(s, bump[i], 1);
		}
	}
    	return 0;
}

void solver_backtrack( Solver *s, int backtrackLevel ) {
    	if ( s->decVarInTrailSize <= backtrackLevel ) return;
	else {
		for ( int i = s->trailSize - 1; i >= s->decVarInTrail[backtrackLevel]; i-- ) {
			int v = abs(s->trail[i]);
			s->value[v] = 0;
			s->saved[v] = s->trail[i] > 0 ? 1 : -1;
			if ( !heap_inHeap(&s->vsids, v) ) heap_insert(&s->vsids, v);
		}
		s->propagated = s->decVarInTrail[backtrackLevel];
		
		for ( int i = s->trailSize; i < s->propagated; i -- ) s->trail[i] = -1;
		s->trailSize = s->propagated;
		
		for ( int i = s->decVarInTrailSize; i < backtrackLevel; i -- ) s->decVarInTrail[i] = -1;
		s->decVarInTrailSize = backtrackLevel;
	}
}

void solver_restart( Solver *s ) {
    	s->fast_lbd_sum = s->lbd_queue_size = s->lbd_queue_pos = 0;
    	solver_backtrack(s, s->decVarInTrailSize);
	s->restarts++;
}

void solver_rephase( Solver *s ) {
	if ( (s->rephases / 2) == 1 ) for ( int i = 1; i <= s->vars; i++ ) s->saved[i] = s->local_best[i];
	else for ( int i = 1; i <= s->vars; i++ ) s->saved[i] = -s->local_best[i];
	solver_backtrack(s, s->decVarInTrailSize);
	s->rephase_inc *= 2;
	s->rephase_limit = s->conflicts + s->rephase_inc;
	s->rephases++;
}

void solver_reduce( Solver *s ) {
    	solver_backtrack(s, 0);
    	s->reduces = 0;
	s->reduce_limit += 512;
    	int new_size = s->origin_clauses;
	int old_size = clauseDBSize;

	if ( old_size > reduceMapSize ) {
		for ( int i = reduceMapSize; i < old_size; i ++ ) reduceMap[i] = -1;
		reduceMapSize = old_size;
	} else {
		for ( int i = reduceMapSize; i < old_size; i -- ) reduceMap[i] = -1;
		reduceMapSize = old_size;
	}

    	for ( int i = s->origin_clauses; i < old_size; i++ ) { 
        	if ( clauseDB[i].lbd >= 5 && rand() % 2 == 0 ) reduceMap[i] = -1; // remove clause
        	else {
            		if ( new_size != i ) clauseDB[new_size] = clauseDB[i];
            		reduceMap[i] = new_size++;
        	}
    	}

	if ( new_size > clauseDBSize ) {
		for ( int i = clauseDBSize; i < new_size; i ++ ) {
			Clause cls_1;
			clause_resize(&cls_1, 0);
			clauseDB[i] = cls_1;
		}
	} else {
		for ( int i = clauseDBSize; i < new_size; i -- ) {
			Clause cls_2;
			clause_resize(&cls_2, 0);
			clauseDB[i] = cls_2;
		}
	}
	clauseDBSize = new_size;

	for ( int v = -s->vars; v <= s->vars; v++ ) {
        	if ( v == 0 ) continue;
        	int old_sz = WatchedPointersSize(v);
		int new_sz = 0;

        	for ( int i = 0; i < old_sz; i++ ) {
            		int old_idx = WatchedPointers(v)[i].clauseIdx;
            		int new_idx = old_idx < s->origin_clauses ? old_idx : reduceMap[old_idx];
            		if ( new_idx != -1 ) {
                		WatchedPointers(v)[i].clauseIdx = new_idx;
                		if (new_sz != i) WatchedPointers(v)[new_sz] = WatchedPointers(v)[i];
                		new_sz++;
            		}
        	}
		WatchedPointersSize(v) = new_sz;
    	}
}

int solver_solve( Solver *s ) {
    	int res = 0;
    	while (!res) {
		int cref = solver_propagate(s);

		if ( cref != -1 ) {
			int backtrackLevel = 0; 
			int lbd = 0;
			res = solver_analyze(s, cref, backtrackLevel, lbd);
			
			if ( res == 20 ) break;
			else {
				solver_backtrack(s, backtrackLevel);
				
				if ( learntSize == 1 ) solver_assign(s, learnt[0], 0, -1);
				else {
					int cref = solver_add_clause(s, learnt, learntSize);
					clauseDB[cref].lbd = lbd;
					solver_assign(s, learnt[0], backtrackLevel, cref);
				}
				s->var_inc *= (1 / 0.8);
				++s->conflicts, ++s->reduces;
				
				if ( s->trailSize > s->threshold ) {
					s->threshold = s->trailSize;
					for ( int i = 1; i < s->vars + 1; i++ ) s->local_best[i] = s->value[i];
				}
			}
		}
		else if ( s->reduces >= s->reduce_limit ) solver_reduce(s);
		else if ( (s->lbd_queue_size == 50) && 
			  (0.8*s->fast_lbd_sum/s->lbd_queue_size > s->slow_lbd_sum/s->conflicts) ) solver_restart(s);
		else if ( s->conflicts >= s->rephase_limit ) solver_rephase(s);
		else res = solver_decide(s);
	}
	return res;
}

