/*@ requires y > 10;
  @ ensures x >= 0;
*/

void f(int x,int y){
	
	if(y>0){
	x = 100;
	x = x+50;
	x = x-100;
	}else{
	x = x-150;
    x = x-100;
	x = x+100;
	}
}
	