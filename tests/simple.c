/*@ requires x >= 0;
  @ ensures x >= 20;
*/

int g(int x){
	x = x - 5;
	x = x * 2;
	return x;
}
