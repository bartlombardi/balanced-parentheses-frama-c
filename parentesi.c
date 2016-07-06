/*@
   logic integer is_l{L}(char c) =
     (c == '(') ? 1:
     0;
*/

/*@
   logic integer is_r{L}(char c) =
     (c == ')') ? 1:
     0;
*/

/*@
    logic integer left{L}(char* c, integer n) =
      (n == 0) ? is_l(c[n]):
      is_l(c[n]) + left(c, n-1);
*/

/*@
    logic integer right{L}(char* c, integer n) =
      (n == 0) ? is_r(c[n]):
      is_r(c[n]) + right(c, n-1);
*/

/*@
   predicate is_balanced{L}(char* c, integer n) =
      left(c, n) == right(c, n) && \forall integer i; 0 <= i <= n ==> left(c, i) >= right(c, i);
*/

/*@ requires \valid(tex + (0..dim-1));
    requires dim > 0;

    behavior balanced:
      assumes is_balanced(tex, dim-1);
      ensures \result == 1;

    behavior unbalanced:
      assumes !is_balanced(tex, dim-1);
      ensures \result == 0;

    complete behaviors balanced, unbalanced;
    disjoint behaviors balanced, unbalanced;
*/

unsigned int bilanciaParentesi(const char* tex, unsigned int dim){

  unsigned int i = 0;
  unsigned int cont_r = 0;
  unsigned int cont_l = 0;
  
  /*@ loop invariant (0 <= i < dim);
      loop assigns i, cont_l, cont_r;
      loop invariant cont_l < dim;
      loop invariant cont_r < dim;
      loop variant dim-i;
   */ 

  while(i < dim){
    if(tex[i] == '('){
      ++cont_l;
      /*@ invariant cont_l == left(tex, i); */
      /*@ invariant tex[i] == '('; */
      /*@ invariant i >= 1 && tex[i] == '(' ==> left(tex, i) == left(tex, i-1)+1; */
    }
    if(tex[i] == ')'){
      ++cont_r;
      /*@ invariant cont_r == right(tex, i); */
      /*@ invariant tex[i] == ')'; */
      /*@ invariant i >= 1 && tex[i] == ')' ==> right(tex, i) == right(tex, i-1)+1; */
      if(cont_r > cont_l){
	/*@ invariant right(tex, i) > left(tex, i); */
	return 0;
      }
    }
    /*@ invariant cont_l == left(tex, i); */
    /*@ invariant cont_r == right(tex, i); */
    /*@ invariant cont_l >= cont_r; */
    /*@ invariant left(tex, i) >= right(tex, i); */
    ++i;
    /*@ invariant 0 <= i <= dim; */
  }

  if(cont_l == cont_r){
    /*@ assert left(tex, dim - 1) == right(tex, dim -1); */
    /*@ assert \forall integer j; 0 <= j <= dim-1 ==> left(tex, j) >= right(tex, j); */
    /*@ assert is_balanced(tex, dim-1); */
    return 1;
  }else{
    /*@ assert !is_balanced(tex, dim-1); */
    return 0;
  }
}
