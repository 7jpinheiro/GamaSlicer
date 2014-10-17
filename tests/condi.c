/*@ requires y >= 0;
  @ ensures  x >= 0;
*/

void g(int y,int x){
	
	if(y>0){
			x = x-150;
			x = x+100;
			x = x+100;
		}else {
			x=x+200;
		}
	x=x+500;

}
