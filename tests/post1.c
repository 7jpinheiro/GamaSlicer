/*@ ensures x >= 0;
*/

void f(int x){
	x = x-150;
	x = x+100;
	x = x+100;
}
	