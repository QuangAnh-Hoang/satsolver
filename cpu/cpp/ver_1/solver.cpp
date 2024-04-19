#include "solver.h"


// Etc
// Elapsed time checker
static inline double timeCheckerCPU(void) {
        struct rusage ru;
        getrusage(RUSAGE_SELF, &ru);
        return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}

// Additional funcs for reading CNF file
uint8_t *read_whitespace( uint8_t *p ) {
        // ASCII
        // Horizontal tab, line feed or new line,
	// vertical tab, form feed or new page, 
	// carriage return, space
        while ( (*p >= 9 && *p <= 13) || *p == 32 ) ++p;
        return p;
}

uint8_t *read_until_new_line( uint8_t *p ) {
        while ( *p != '\n' ) {
                if ( *p++ == '\0' ) exit(1);
        }
        return ++p;
}

uint8_t *read_int( uint8_t *p, int *i ) {
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


// Solver
// Allocate memory and initialize the values
void Solver::initialize() {
    	value  = new int8_t[vars + 1];
    	local_best = new int8_t[vars + 1];
	saved = new int8_t[vars + 1];
	reason = new int[vars + 1];
    	level = new int[vars + 1];
    	mark = new int[vars + 1];
    	activity = new double[vars + 1];
    	watched_literals = new std::vector<WL>[vars * 2 + 1]; // Two polarities
    	
	conflicts = decides = propagations = 0;
	restarts = rephases = reduces = 0;
    	threshold = propagated = time_stamp = 0;
	fast_lbd_sum = lbd_queue_size = lbd_queue_pos = slow_lbd_sum = 0;

    	var_inc = 1;
	var_decay = 0.8;
	rephase_inc = 1e5, rephase_limit = 1e5, reduce_limit = 8192; // Heuristics

	vsids.initialize(activity);
    	for (int i = 1; i <= vars; i++) {
        	value[i] = reason[i] = level[i] = mark[i] = local_best[i] = activity[i] = saved[i] = 0;
		vsids.insert(i);
    	}
}

// Assign true value to a certain literal
void Solver::assign( int literal, int l, int cref ) {
    	int var = abs(literal);
	// Only make it ture
	// The same literal but has opposite polarity gonna be false
    	value[var]  = literal > 0 ? 1 : -1;
    	level[var]  = l;
	reason[var] = cref;                                         
    	trail.push_back(literal);
}

// Add a clause to the database
int Solver::add_clause( std::vector<int> &c ) {                   
    	clauseDB.push_back(Clause(c.size()));                          
    	
	int id = clauseDB.size() - 1;                                
    	for ( int i = 0; i < (int)c.size(); i++ ) clauseDB[id][i] = c[i];
        
	// There's two watched literals
	// Store each of two literals to the array of its opposite one
	// We only assign True value
	// If we assign c[0] as true, the only concern is -c[0]
	// c[1] is a blocker for c[0] and vice versa
    	WatchedLiterals(-c[0]).push_back(WL(id, c[1])); // watched_literals[vars-c[0]]                      
    	WatchedLiterals(-c[1]).push_back(WL(id, c[0])); // watched_literals[vars-c[1]]

    	return id;                                                      
}

// BCP (Boolean Constraint Propagation)
int Solver::propagate() {
	// This propagate style is fully based on MiniSAT
    	while ( propagated < (int)trail.size() ) { 
		// 'p' is already assigned as true
		// We now gonna only concern '-p'
        	int p = trail[propagated++];
        	// Take an array of '-p'
		std::vector<WL> &ws = WatchedLiterals(p);
		// Check all clauses that contains '-p'
		int num_clauses = ws.size();
		int j = 0;
		for ( int i = 0; i < num_clauses;  ) {
			// To make the BCP progess fast
			// Check whether a clause is already satisfied via blocker
			// If then, move to the next clause that has '-p'
            		int blocker = ws[i].blocker;                       
			if ( Value(blocker) == 1 ) {                
                		ws[j++] = ws[i++]; 
				continue;
            		}
			// We only take care of the position c[0], c[1]
			// If we have to find a new wathced literal,
			// We gonna move the literal's position to c[1]
            		// Make sure the false literal is 'c[1]'
			int cref = ws[i].clauseIdx;
			Clause& c = clauseDB[cref];
			int falseLiteral = -p; 
            		if ( c[0] == falseLiteral ) {
				c[0] = c[1];
				c[1] = falseLiteral;
			}
			i++;
			// Let's first check 0th watched literal
			// If 0th watched literal is true, then clause is already satisfied
			int firstWP = c[0];
			WL w = WL(cref, firstWP);
			if ( Value(firstWP) == 1 ) {                   
                		ws[j++] = w; 
				continue;
            		}
			// Look for a new watched literal in this clause
			int k;
			int sz = c.literals.size();
            		for ( k = 2; (k < sz) && (Value(c[k]) == -1); k++ ); 
			if ( k < sz ) {
				// Find it!
				// Move '-p' to the last position that has also false value
                		c[1] = c[k];
				c[k] = falseLiteral;
				// Make c[0] as blocker
                		WatchedLiterals(-c[1]).push_back(w);
			} else { 
				// Couldn't find a new watched literal
				// then, clause is unit under assignment
				ws[j++] = w;
				// Conflict!
				// This means all literals are false
				// including c[0] and '-p'
                		if ( Value(firstWP) == -1 ) { 
                    			while ( i < num_clauses ) ws[j++] = ws[i++];
					// Shrink
                    			ws.resize(j);
					// Return the index of clause
                    			return cref;
                		}
				// Not conflict!
				// then, assign!
                		else {
					assign(firstWP, level[abs(p)], cref);
					propagations++;
				}
			}
            	}
		// Shrink
        	ws.resize(j);
    	}
    	return -1;                                       
}

// Read CNF file
int Solver::parse( char *filename ) {
    	FILE *f_data = fopen(filename, "r");  

	// Get the file size first
    	fseek(f_data, 0, SEEK_END);
    	size_t file_len = ftell(f_data);

	// Then read the file
	fseek(f_data, 0, SEEK_SET);
	uint8_t *data = new uint8_t[file_len + 1];
	uint8_t *p = data;
	fread(data, sizeof(uint8_t), file_len, f_data);
	fclose(f_data);                                             
	data[file_len] = '\0';

	// Save a clause temporarily to go to the database
    	std::vector<int> buffer;

	// Parse the file
	while ( *p != '\0' ) {
        	p = read_whitespace(p);
        	
		if ( *p == '\0' ) break;
		// If there are some comments in CNF file
        	if ( *p == 'c' ) p = read_until_new_line(p);
       	 	else if ( *p == 'p' ) { 
            		if ( (*(p + 1) == ' ') && (*(p + 2) == 'c') && 
			     (*(p + 3) == 'n') && (*(p + 4) == 'f') ) {
                		p += 5; 
				p = read_int(p, &vars); 
				p = read_int(p, &clauses);
                		initialize();
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
    	origin_clauses = clauseDB.size();
    	return ( propagate() == -1 ? 0 : 20 );             
}

// Pick decision variable based on VSIDS
int Solver::decide() {      
    	int next = -1;
	while ( next == -1 || Value(next) != 0 ) {
        	if (vsids.empty()) return 10;
        	else next = vsids.pop();
    	}
    	decVarInTrail.push_back(trail.size());
    	
	// If there's saved one (polarity), use that
	if ( saved[next] ) next *= saved[next];
    	assign(next, decVarInTrail.size(), -1);

    	decides++;
	return 0;
}

// Update activity
void Solver::update_score( int var, double coeff ) {
	// Update score and prevent overflow
	// Double type bumping scheme
	if ( (activity[var] += var_inc * coeff) > 1e100 ) {
		for ( int i = 1; i <= vars; i ++ ) activity[i] *= 1e-100;
		var_inc *= 1e-100;
	}
	// Update Heap
    	if ( vsids.inHeap(var) ) vsids.update(var);
}

// Conflict analysis
int Solver::analyze( int conflict, int &backtrackLevel, int &lbd ) {
	// This analysis is based on 'First UIP Learning Method'
	// Unit Implication Points
	// The main motivation for identifying UIPs is to reduce the size of learnt clauses
	// In the implication graph, 
	// there is a UIP at decision level d,
	// when the number of literals in intermediate clause
	// assigned at decision level d is 1
    	++time_stamp;
    	learnt.clear();
    	Clause &c = clauseDB[conflict]; 
	int conflictLevel = level[abs(c[0])];

    	if ( conflictLevel == 0 ) return 20; // UNSAT
	else {
		// Leave a place to save the first UIP
		learnt.push_back(0);
		// # of literals 
		// that have not visited
		// in the conflict level of the implication graph
		int should_visit_ct = 0;
		// The literal to do resolution
		int resolve_lit = 0;
		int index = trail.size() - 1;

		// Store variables in a certain clause temporarily
		std::vector<int> bump;
		do {
			// First UIP learning method
			Clause &c = clauseDB[conflict];
			// Mark the literals
			for ( int i = (resolve_lit == 0 ? 0 : 1); i < (int)c.literals.size(); i++ ) {
				int var = abs(c[i]);
				if ( mark[var] != time_stamp && level[var] > 0 ) {
					// Update score (step 1)
					update_score(var, 0.5);
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
		
		// Sum of the recent 50 LBDs
		fast_lbd_sum += lbd;
		lbd_queue[lbd_queue_pos++] = lbd;
		
		// Sum of the global LBDs
		if ( lbd_queue_pos == 50 ) lbd_queue_pos = 0;
		slow_lbd_sum += (lbd > 50 ? 50 : lbd);
			
		// Decide backtrack level
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

		// Update score (step 2)
		for ( int i = 0; i < (int)bump.size(); i++ ) {   
			if ( level[bump[i]] >= backtrackLevel - 1 ) update_score(bump[i], 1);
		}
	}
    	return 0;
}

// Backtracking
void Solver::backtrack( int backtrackLevel ) {
    	if ( (int)decVarInTrail.size() <= backtrackLevel ) return;
	else {
		for ( int i = trail.size() - 1; i >= decVarInTrail[backtrackLevel]; i-- ) {
			int v = abs(trail[i]);
			value[v] = 0;
			// Phase saving
			saved[v] = trail[i] > 0 ? 1 : -1;
			// Store variable back to VSIDS heap
			if ( !vsids.inHeap(v) ) vsids.insert(v);
		}
		propagated = decVarInTrail[backtrackLevel];
		trail.resize(propagated);
		decVarInTrail.resize(backtrackLevel);
	}
}

// Do restart
void Solver::restart() {
    	fast_lbd_sum = lbd_queue_size = lbd_queue_pos = 0;
    	backtrack(decVarInTrail.size());
	restarts++;
}

// Do rephase
void Solver::rephase() {
	// This rephase style is fully based on CaDiCaL
	if ( rephases/2 == 1 ) for ( int i = 1; i <= vars; i++ ) saved[i] = local_best[i];
	else for ( int i = 1; i <= vars; i++ ) saved[i] = -local_best[i];
	backtrack(decVarInTrail.size());
	rephase_inc *= 2;
	rephase_limit = conflicts + rephase_inc;
	rephases++;
}

// Do reduce
void Solver::reduce() {
	// Go back to the first decision level first
    	backtrack(0);

    	reduces = 0;
	reduce_limit += 512;
    	
	int new_size = origin_clauses;
	int old_size = clauseDB.size();

	reduceMap.resize(old_size);
	
	// Random delete 50% bad clauses (LBD>=5) 
	// Reducing based on Literal Block Distances
    	for ( int i = origin_clauses; i < old_size; i++ ) { 
        	if ( clauseDB[i].lbd >= 5 && rand() % 2 == 0 ) reduceMap[i] = -1;
        	else {
            		if ( new_size != i ) clauseDB[new_size] = clauseDB[i];
            		reduceMap[i] = new_size++;
        	}
    	}

	// Resize the clause database
    	clauseDB.resize(new_size, Clause(0));
    	
	// Update the array of watched literals
	for ( int v = -vars; v <= vars; v++ ) {
        	if ( v == 0 ) continue;

        	int old_sz = WatchedLiterals(v).size();
		int new_sz = 0;

        	for ( int i = 0; i < old_sz; i++ ) {
            		int old_idx = WatchedLiterals(v)[i].clauseIdx;
            		int new_idx = old_idx < origin_clauses ? old_idx : reduceMap[old_idx];
            		if ( new_idx != -1 ) {
                		WatchedLiterals(v)[i].clauseIdx = new_idx;
                		if (new_sz != i) WatchedLiterals(v)[new_sz] = WatchedLiterals(v)[i];
                		new_sz++;
            		}
        	}
        	WatchedLiterals(v).resize(new_sz);
    	}
}

// Solver
int Solver::solve() {
    	int res = 0;
	double processStart = timeCheckerCPU();
    	
	while (!res) {
		double processFinish = timeCheckerCPU();
		double processTime = processFinish - processStart;

		if ( processTime < 2000 ) {
			int cref = propagate();
		
			// Find a conflict
			if ( cref != -1 ) {
				int backtrackLevel = 0; 
				int lbd = 0;
				
				res = analyze(cref, backtrackLevel, lbd);
			
				if ( res == 20 ) {
					// Find a conflict in 0 decision level
					// UNSAT
					break;
				} else {
					backtrack(backtrackLevel);
				
					if ( learnt.size() == 1 ) {
						// Learnt a clause (unit)
						// No need to add to clause database
						// Directly assigning!
						assign(learnt[0], 0, -1);
					} else {
						// Learnt a clause (not unit)
						// Add a clause to clause database
						int cref = add_clause(learnt);
						clauseDB[cref].lbd = lbd;
						// The learnt clause implies the assignment of the UIP variable
						assign(learnt[0], backtrackLevel, cref); 
					}

					// var_decay for locality
					var_inc *= (1 / var_decay);

					++conflicts, ++reduces;
					
					// Update the local-best phase
					if ( (int)trail.size() > threshold ) {
						threshold = trail.size();
						for ( int i = 1; i < vars + 1; i++ ) local_best[i] = value[i];
					}
				}
			} else if ( reduces >= reduce_limit ) {
				reduce();
			} else if ( lbd_queue_size == 50 && 0.8*fast_lbd_sum/lbd_queue_size > slow_lbd_sum/conflicts ) {
				restart();
			} else if ( conflicts >= rephase_limit ) {
				rephase();
			} else {
				res = decide();
			}
		} else res = 30;
	}

	if ( res == 10 || res == 20 ) {
		double processFinal = timeCheckerCPU();
		double processTimeFinal = processFinal - processStart;
		printf( "Elapsed Time (CPU): %.2f\n", processTimeFinal );
        printf( "Conflicts: %d\n", conflicts );
		printf( "Decisions: %d\n", decides );
		printf( "Propagations: %d\n", propagations );
		printf( "Evaluations: %d\n", propagations + decides );
	}

	return res;
}

// Print model when the result is SAT
void Solver::printModel() {
    	for ( int i = 1; i <= vars; i++ ) printf("%d ", value[i] * i);
    	printf( "0\n" );
}
