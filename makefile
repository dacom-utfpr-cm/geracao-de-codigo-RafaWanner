# Makefile para deletar arquivos .ast.dot, .unique.ast.dot e .unique.ast.png na pasta tests

# Diretório alvo
DIRTEST = tests

# Padrões de arquivos
LL = $(DIRTEST)/*.ll
AST_DOT = $(DIRTEST)/*.ast.dot
UNIQUE_AST_DOT = $(DIRTEST)/*.unique.ast.dot
UNIQUE_AST_PNG = $(DIRTEST)/*.unique.ast.png

run:
	@export LD_LIBRARY_PATH=/path/to/libs; \
	python3 tppgencode.py ./tests/$(DIR).tpp -k; \
	echo "\nExecuting:\n"; \
	clang -c tests/io.c -S -emit-llvm -o io.ll; \
	llvm-link tests/$(DIR).ll io.ll -o $(DIR)-link.ll; \
	clang $(DIR)-link.ll; \
	echo "\nRunning $(DIR):\n"; \
	./a.out; \
	sla=$$?; echo "\nExit code: $$sla\n"; \
	rm ./a.out; \
	rm ./io.ll; \
	rm ./$(DIR)-link.ll; \
	rm ./tests/$(DIR).ll; \
	rm ./tests/$(DIR).tpp.ast.dot; \
	rm ./tests/$(DIR).tpp.unique.ast.dot; \
	rm ./tests/$(DIR).tpp.unique.ast.png

run_not_delete:
	@export LD_LIBRARY_PATH=/path/to/libs; \
	python3 tppgencode.py ./tests/$(DIR).tpp -k; \
	echo "\nExecuting:\n"; \
	clang -c tests/io.c -S -emit-llvm -o io.ll; \
	llvm-link tests/$(DIR).ll io.ll -o $(DIR)-link.ll; \
	clang $(DIR)-link.ll; \
	echo "\nRunning $(DIR):\n"; \
	./a.out; \
	sla=$$?; echo "\nExit code: $$sla\n"

# Alvo para deletar todos os arquivos
clean:
	@echo "Deletando arquivos *.ast.dot, *.unique.ast.dot e *.unique.ast.png no diretório $(DIRTEST)..."
	@rm -f $(LL) $(AST_DOT) $(UNIQUE_AST_DOT) $(UNIQUE_AST_PNG)
	@echo "Arquivos deletados."

# Alvo padrão
.PHONY: run
.PHONY: clean
