/*@ ensures x >= 100;
*/

void f(int x){
	x = x*x;
	x = x+100;
	x = x+50;
}
		