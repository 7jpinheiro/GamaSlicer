/*@ requires x >= 0;
  @ ensures x >= y;
*/

int g(int x,int y){
	if(x < y){
		x = y; 
	}
	return x;
}
