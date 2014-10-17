/*@ requires x >= 0;
*/

void f(int x){
	
	if(x>0){
	x = x+100;
	x = x-200;
	x = x+200;
	}else{
	x = x-150;
    x = x-100;
	x = x+100;
	}
}
	