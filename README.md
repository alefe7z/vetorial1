# Vetorial

Editor de desenho vetorial simples para Windows, feito em Python (Tkinter).

## Recursos
- Ferramentas: selecionar/mover (V), retângulo (R), elipse (E), linha (L), lápis (P), texto (T)
- Cor de contorno, cor de preenchimento e espessura
- Shift ao desenhar: quadrado/círculo perfeito e linha a 45°
- Desfazer/refazer (Ctrl+Z / Ctrl+Y), duplicar (Ctrl+D), excluir (Del)
- Trazer para frente / enviar para trás (Ctrl+] / Ctrl+[)
- Setas movem a forma selecionada (Shift+seta = 10 px)
- Duplo clique em um texto para editar
- Salvar/abrir arquivos `.vetorial` e exportar para SVG (Ctrl+E)

## Como gerar o .exe
O arquivo `.github/workflows/build.yml` faz o GitHub gerar o `Vetorial.exe`
automaticamente a cada atualização. Veja em **Actions → última execução → Artifacts**.

## Rodar sem gerar .exe
Com Python instalado: `python main.py`
