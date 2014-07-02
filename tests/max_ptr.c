

/*@ requires \valid(p) && \valid(q); 
    ensures *p <= *q; 
    behavior p_minimum: 
      assumes *p < *q; 
      ensures *p == \old(*p) && *q == \old(*q); 
    behavior q_minimum: 
      assumes *p >= *q; 
      ensures *p == \old(*q) && *q == \old(*p); 
    complete behaviors p_minimum, q_minimum; 
    disjoint behaviors p_minimum, q_minimum; 
*/
void max_ptr(int*p, int*q) { 
  if (*p > *q) { 
    int tmp = *p; 
    *p = *q; 
    *q = tmp; 
  } 
} 