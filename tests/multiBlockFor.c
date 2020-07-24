int main(){
	int a = 1;
	int b = a;
	for(int i = 0;i < 2;i++){
		a = a + b;
	}
	return b;
}
