default:
	@latexmk --pdflua -synctex=1 --shell-escape --pv $(tex)

clean:
	@git clean -dfX
