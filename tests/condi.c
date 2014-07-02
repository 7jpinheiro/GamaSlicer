/*@ requires y >= 0;
  @ ensures \result >= 0;
*/

int g(int y){
	int x=0;
	
	if(y>0){
		x=100;
		x=x+50;
		x=x-100;
		/*@ assert x >=0 ; */
	}
	return x;
}
