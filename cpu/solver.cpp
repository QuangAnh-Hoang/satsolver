#include "solver.h"
#include <fstream>
#include <time.h>

#define Value(literal) (literal > 0 ? value[literal] : -value[-literal])
#define WatchPointer(id) (watchedPointers[vars + id])


// Elapsed time checker
double timespec_diff_sec( timespec start, timespec end ) {
	double t = end.tv_sec - start.tv_sec;
	t += ((double)(end.tv_nsec - start.tv_nsec)/1000000000L);
	return t;
}


// Functions for parser
char *read_whitespace( char *p ) {      
	// ASCII
	// Horizontal tab, line feed or new line, vertical tab, form feed or new page, carriage return, space	
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
    	bool sym = true; 
	*i = 0;
    	p = read_whitespace(p);
    	if ( *p == '-' ) {
		sym = false;
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


// Functions for Solver
int Solver::add_clause( std::vector<int> &c ) {                   
    	clause_DB.push_back(Clause(c.size()));                          
    	int id = clause_DB.size() - 1;                                
    	for ( int i = 0; i < (int)c.size(); i++ ) clause_DB[id][i] = c[i];
        // There's two watched literals	
    	WatchPointer(-c[0]).push_back(WL(id, c[1])); // watchedPointers[vars-c[0]]                      
    	WatchPointer(-c[1]).push_back(WL(id, c[0])); // watchedPointers[vars-c[1]]
    	return id;                                                      
}

int Solver::parse( char *filename ) {
    	std::ifstream fin(filename);  

    	fin.seekg(0, fin.end);
    	size_t file_len = fin.tellg();

	fin.seekg(0, fin.beg);
	char *data = new char[file_len + 1];
	char *p = data;
	fin.read(data, file_len);
	fin.close();                                             
	
	data[file_len] = '\0';
    	std::vector<int> buffer; // Save the clauses temporarily
    	while ( *p != '\0' ) {
        	p = read_whitespace(p);
        	if ( *p == '\0' ) break;
        	if ( *p == 'c' ) p = read_until_new_line(p); // If there are some comments in CNF
       	 	else if ( *p == 'p' ) { 
            		if ( (*(p + 1) == ' ') && (*(p + 2) == 'c') && 
			     (*(p + 3) == 'n') && (*(p + 4) == 'f') ) {
                		p += 5; 
				p = read_int(p, &vars); 
				p = read_int(p, &clauses);
                		alloc_memory();
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
				else buffer.push_back(dimacs_lit);
			}
			else {                                                       
                		if ( buffer.size() == 0 ) return 20;
				else if ( buffer.size() == 1 ) {
					if ( Value(buffer[0]) == -1 ) return 20;
					else if ( !Value(buffer[0]) ) assign(buffer[0], 0, -1);
				}
                		else add_clause(buffer); 

                		buffer.clear();                                        
            		}
        	}
    	}
    	origin_clauses = clause_DB.size();
    	return ( propagate() == -1 ? 0 : 20 );             
}

void Solver::alloc_memory() {
    	value  = new int[vars + 1];
    	reason = new int[vars + 1];
    	level = new int[vars + 1];
    	mark = new int[vars + 1];
    	local_best = new int[vars + 1];
    	saved = new int[vars + 1];
    	activity = new double[vars + 1];
    	watchedPointers = new std::vector<WL>[vars * 2 + 1]; // Two polarities
    	
	conflicts = time_stamp = propagated = restarts = rephases = reduces = threshold = 0;
    	fast_lbd_sum = lbd_queue_size = lbd_queue_pos = slow_lbd_sum = 0;
    	var_inc = 1, rephase_limit = 1024, reduce_limit = 8192;

    	// Initialization	
	vsids.setComp(GreaterActivity(activity));
    	for (int i = 1; i <= vars; i++) {
        	value[i] = reason[i] = level[i] = mark[i] = local_best[i] = activity[i] = saved[i] = 0;
		vsids.insert(i);
    	}
}

void Solver::assign( int literal, int l, int cref ) {
    	int var = abs(literal);
    	value[var]  = literal > 0 ? 1 : -1;
    	level[var]  = l;
	reason[var] = cref;                                         
    	trail.push_back(literal);
}

int Solver::decide() {      
    	int next = -1;
	// Pick up a variable based on VSIDS
	while ( next == -1 || Value(next) != 0 ) {
        	if (vsids.empty()) return 10;
        	else next = vsids.pop();
    	}
    	decVarInTrail.push_back(trail.size());
    	// If there's saved one(polarity), use that
	if ( saved[next] ) next *= saved[next];

    	assign(next, decVarInTrail.size(), -1);
    	
	return 0;
}

int Solver::propagate() {
	// This propagate style is fully based on MiniSAT
    	while ( propagated < (int)trail.size() ) { 
        	int p = trail[propagated++]; // 'p' is enqueued fact to propagate
        	std::vector<WL> &ws = WatchPointer(p);
		int size = ws.size();
        	int i, j;                     
        	for ( i = j = 0; i < size;  ) {
			// Try to avoid inspecting the clause
            		int blocker = ws[i].blocker;                       
			if ( Value(blocker) == 1 ) {                
                		ws[j++] = ws[i++]; 
				continue;
            		}
            		// Make sure the false literal is 'c[1]'
			int cref = ws[i].clauseIdx;
			int falseLiteral = -p;
            		Clause& c = clause_DB[cref];              
            		if ( c[0] == falseLiteral ) {
				c[0] = c[1];
				c[1] = falseLiteral;
			}
			i++;
			// If 0th watch pointer is true, then clause is already satisfied
			int firstWP = c[0];
			WL w = WL(cref, firstWP);
			if ( Value(firstWP) == 1 ) {                   
                		ws[j++] = w; 
				continue;
            		}
			// Look for new watch pointer
			int k;
			int sz = c.literals.size();
            		for ( k = 2; (k < sz) && (Value(c[k]) == -1); k++ ); 
			if ( k < sz ) {                           
                		c[1] = c[k];
				c[k] = falseLiteral;
                		WatchPointer(-c[1]).push_back(w);
			}         
			else { // Did not find new watch, clause is unit under assignment
				ws[j++] = w;
				// Conflict!
                		if ( Value(firstWP) == -1 ) { 
                    			while ( i < size ) ws[j++] = ws[i++];
					// Shrink
                    			ws.resize(j);
                    			return cref;
                		}
				// Not conflict!
                		else assign(firstWP, level[abs(p)], cref);
			}
            	}
		// Shrink
        	ws.resize(j);
    	}
    	return -1;                                       
}

void Solver::bump_var( int var, double coeff ) {
	// Update score and prevent float overflow
    	if ( (activity[var] += var_inc * coeff) > 1e100 ) {
        	for ( int i = 1; i <= vars; i++ ) activity[i] *= 1e-100;
        	var_inc *= 1e-100;
	}
	// Update Heap
    	if ( vsids.inHeap(var) ) vsids.update(var);
}

int Solver::analyze( int conflict, int &backtrackLevel, int &lbd ) {
    	++time_stamp;
    	learnt.clear();
    	Clause &c = clause_DB[conflict]; 
	int conflictLevel = level[abs(c[0])];

    	if ( conflictLevel == 0 ) return 20; // UNSAT
	else {
		learnt.push_back(0); // Leave a place to save the first UIP
		std::vector<int> bump;
		int should_visit_ct = 0; // The number of literals that have not visited in the conflict level of the implication graph
		int resolve_lit = 0; // The literal to do resolution
		int index = trail.size() - 1;
		// First UIP learning method
		do {
			Clause &c = clause_DB[conflict];
			// Mark the literals
			for ( int i = (resolve_lit == 0 ? 0 : 1); i < (int)c.literals.size(); i++ ) {
				int var = abs(c[i]);
				if ( mark[var] != time_stamp && level[var] > 0 ) {
					bump_var(var, 0.5);
					bump.push_back(var);
					mark[var] = time_stamp;
					if ( level[var] >= conflictLevel ) should_visit_ct++;
					else learnt.push_back(c[i]);
				}
			}
			// Find the last marked literal in the trail to do resolution
			do {
				while ( mark[abs(trail[index--])] != time_stamp );
				resolve_lit = trail[index + 1];
			} while ( level[abs(resolve_lit)] < conflictLevel );
			
			conflict = reason[abs(resolve_lit)];
			mark[abs(resolve_lit)] = 0;
			should_visit_ct--;
		} while ( should_visit_ct > 0 );

		learnt[0] = -resolve_lit;
		++time_stamp;
		lbd = 0;
		
		// Calculate LBD
		for ( int i = 0; i < (int)learnt.size(); i++ ) {
			int l = level[abs(learnt[i])];
			if ( l && mark[l] != time_stamp ) {
				mark[l] = time_stamp;
				++lbd;
			}
		}

		if ( lbd_queue_size < 50 ) lbd_queue_size++;
		else fast_lbd_sum -= lbd_queue[lbd_queue_pos];
		
		fast_lbd_sum += lbd; // Sum of the recent 50 LBDs
		lbd_queue[lbd_queue_pos++] = lbd;
		
		if ( lbd_queue_pos == 50 ) lbd_queue_pos = 0;
		slow_lbd_sum += (lbd > 50 ? 50 : lbd); // Sum of the global LBDs
			
		if ( learnt.size() == 1 ) backtrackLevel = 0;
		else {
			int max_id = 1;
			for ( int i = 2; i < (int)learnt.size(); i++ ) {
				if ( level[abs(learnt[i])] > level[abs(learnt[max_id])] ) max_id = i;
			}
			int p = learnt[max_id];
			learnt[max_id] = learnt[1];
			learnt[1] = p;
			backtrackLevel = level[abs(p)];
		}

		for ( int i = 0; i < (int)bump.size(); i++ ) {   
			if ( level[bump[i]] >= backtrackLevel - 1 ) bump_var(bump[i], 1);
		}
	}
    	return 0;
}

void Solver::backtrack( int backtrackLevel ) {
    	if ( (int)decVarInTrail.size() <= backtrackLevel ) return;
	else {
		for ( int i = trail.size() - 1; i >= decVarInTrail[backtrackLevel]; i-- ) {
			int v = abs(trail[i]);
			value[v] = 0;
			saved[v] = trail[i] > 0 ? 1 : -1; // Phase saving
			if ( !vsids.inHeap(v) ) vsids.insert(v); // Update heap
		}
		propagated = decVarInTrail[backtrackLevel];
		trail.resize(propagated);
		decVarInTrail.resize(backtrackLevel);
	}
}

void Solver::restart() {
    	fast_lbd_sum = lbd_queue_size = lbd_queue_pos = 0;
    	backtrack(0);
    	int phase_rand = rand() % 100;
    	if ((phase_rand -= 60) < 0) for (int i = 1; i <= vars; i++) saved[i] = local_best[i];
    	else if ((phase_rand -= 5) < 0) for (int i = 1; i <= vars; i++) saved[i] = -local_best[i];
    	else if ((phase_rand -= 20) < 0) for (int i = 1; i <= vars; i++) saved[i] = rand() % 2 ? 1 : -1;
}

void Solver::rephase() {
    	rephases = 0, threshold *= 0.9, rephase_limit += 8192;
}

void Solver::reduce() {
    	backtrack(0);
    	reduces = 0;
	reduce_limit += 512;
    	int new_size = origin_clauses;
	int old_size = clause_DB.size();
    	reduce_map.resize(old_size);
	// Random delete 50% bad clauses (LBD>=5) 
	// Reducing based on Literal Block Distances
    	for ( int i = origin_clauses; i < old_size; i++ ) { 
        	if ( clause_DB[i].lbd >= 5 && rand() % 2 == 0 ) reduce_map[i] = -1; // remove clause
        	else {
            		if ( new_size != i ) clause_DB[new_size] = clause_DB[i];
            		reduce_map[i] = new_size++;
        	}
    	}
    	clause_DB.resize(new_size, Clause(0));
    	for ( int v = -vars; v <= vars; v++ ) { // Update Watched Pointers
        	if ( v == 0 ) continue;
        	int old_sz = WatchPointer(v).size();
		int new_sz = 0;

        	for ( int i = 0; i < old_sz; i++ ) {
            		int old_idx = WatchPointer(v)[i].clauseIdx;
            		int new_idx = old_idx < origin_clauses ? old_idx : reduce_map[old_idx];
            		if ( new_idx != -1 ) {
                		WatchPointer(v)[i].clauseIdx = new_idx;
                		if (new_sz != i) WatchPointer(v)[new_sz] = WatchPointer(v)[i];
                		new_sz++;
            		}
        	}
        	WatchPointer(v).resize(new_sz);
    	}
}

int Solver::solve() {
    	int res = 0;
    	while (!res) {
		int cref = propagate(); // Boolean Constraint Propagation (BCP)
		// Find a conflict
		if ( cref != -1 ) {
			int backtrackLevel = 0; 
			int lbd = 0;
			res = analyze(cref, backtrackLevel, lbd); // Conflict analyze
			
			if ( res == 20 ) break; // Find a conflict in 0 decision level
			else {
				backtrack(backtrackLevel); // backtracking
				
				if ( learnt.size() == 1 ) assign(learnt[0], 0, -1); // Learnt a unit clause
				else {
					int cref = add_clause(learnt); // Add a clause to data base.
					clause_DB[cref].lbd = lbd;
					assign(learnt[0], backtrackLevel, cref); // The learnt clause implies the assignment of the UIP variable.
				}
				var_inc *= (1 / 0.8); // var_decay for locality
				++restarts, ++conflicts, ++rephases, ++reduces;
				
				// Update the local-best phase
				if ( (int)trail.size() > threshold ) {
					threshold = trail.size();
					for ( int i = 1; i < vars + 1; i++ ) local_best[i] = value[i];
				}
			}
		}
		else if ( reduces >= reduce_limit ) reduce();
		else if ( (lbd_queue_size == 50) && (0.8*fast_lbd_sum/lbd_queue_size > slow_lbd_sum/conflicts) ) restart();
		else if ( rephases >= rephase_limit ) rephase();
		else res = decide();
	}
	return res;
}

void Solver::printModel() {
    	for ( int i = 1; i <= vars; i++ ) printf("%d ", value[i] * i);
    	printf( "0\n" );
}

int main( int argc, char **argv ) {
    	timespec start;
    	timespec now;
    
	Solver S;
    
	clock_gettime(CLOCK_REALTIME, &start);
    	int res = S.parse(argv[1]);
    	clock_gettime(CLOCK_REALTIME, &now);
    	double diff = timespec_diff_sec(start, now);
    	printf( "Parsing Time: %f\n", diff );
    
	if ( res == 20 ) printf("s UNSATISFIABLE\n");
    	else {
		clock_gettime(CLOCK_REALTIME, &start);
        	res = S.solve();
        	if ( res == 10 ) {
           		 printf("s SATISFIABLE\n");
            		S.printModel();
        	}
        	else if ( res == 20 ) printf("s UNSATISFIABLE\n");
		clock_gettime(CLOCK_REALTIME, &now);
		diff = timespec_diff_sec(start, now);
		printf( "Elapsed Time: %f\n", diff );
    	}
    	return 0;
}
