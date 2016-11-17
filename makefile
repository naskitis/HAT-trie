compile_all:
#standard chain data structures
	gcc -O3 -fomit-frame-pointer -Wno-format -DEXACT_FIT -o nikolas_askitis_hat_trie nikolas_askitis_hat_trie.c
#quick usage quide
	@echo
	@cat USAGE_POLICY.txt;
	@echo "\nUsage  eg: ./array-hash-exact 65536  2  insert-file01 insert-file02  1  search-file01"
	@echo "           ./standard-bst  1  insert-file01  3  search-file01 search-file02 search-file03";
	@echo "           ./array-burst-trie-exact  256  1 insert-file01 1 search-file01";
	@echo;
	@echo "Output eg: 'Array-BST 24.79 6.17 6.17 1000000 1000000' = data struct, space(MB), insert(sec), search(sec), inserted, found ";
	@echo;
	@echo "Dr. Nikolas Askitis | Copyright @ 2016 | askitisn@gmail.com"
	@echo;
clean:
	rm -rf t*[!.c]
	rm -rf n*[!.c]
	rm -rf s*[!.c]
