/*@ requires y >= 0;
  @ ensures  x >= 0;
*/

void g(int y,int x){
	
	if(y>0){
		x=100;
		x=x+50;
		x=x-100;
	}
   x=x+200;	
}
