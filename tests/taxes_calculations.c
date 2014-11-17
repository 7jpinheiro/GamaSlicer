/*@ requires age >= 18;
  @ ensures personal >= 5750;
*/

void taxesCalculation(int age, int income, int personal, int t){

	if(age >= 75){ personal = 5980; }
	else if(age >= 65){ personal = 5720; }
		 else { personal = 4335; }

	if((age >= 65) && (income > 16800))
	{
		t = personal - ((income -16800)/2);
		if (t > 4335){ personal = t + 2000; }
		else { personal = 4335; }
	}
}