import Game.Levels.Intro
import Game.Levels.Intermediate
--import Game.Levels.DemoWorld

-- Here's what we'll put on the title screen
Title "CAP GAME"
Introduction
"
# CAP GAME
Learn to use computers to formalize proofs!

# What is this game?

In this game, you will learn the basics of how a program called a *proof assistant* works and use
it to formalize some mathematical results.
What does this mean? Instead of writing down proofs in English or any other human language we will
explain the steps of the proof to the proof assistant using a precise language, similar to a
programming language in some aspects.
The advantage of doing this is that the computer can then keep track of the proof for us, and tell
us if we make any steps that aren't logically valid, computers are very good at understanding logic
after all!
Other than needing to use specific commands to explain the proof steps, we can work on proofs like
usual, using definitions and already established facts to show new results.
The proof assistant will completely keep track of what facts we know so far, and show us what else
needs to be shown to finish the current proof. Importantly, it won't let us show something that
doesn't logically follow from what we have proved so far.

This is a very literal sort of computer assisted proof, we are using a computer to step through and
understand individual steps in a proof.
Later we will see how the assistant can do more than just follow our instructions, it can also
search for us and find useful facts we might want to use. Lean can even complete some moderately
difficult or tricky proofs on its own, using proof methods based on pre-defined rules.
This saves us time thinking about details in some situations, without losing any confidence in the
correctness of the result, and in some cases we can even learn from the proofs Lean finds!


To get started click on the first world, the circle labeled Intro, on the right.
You can use this menu to navigate as you try more of the problems.
Have fun!

If you experience any technical issues with the game please let us know on the canvas page.
"

Info "
The CAP Game, was created as material for the course computer assisted proofs at the Vrije Universiteit Amsterdam.
The original version can be found here https://alexjbest.github.io/CAP-game/.
Based on templates from Imperial College London and Universitat Autònoma de Barcelona.
This version is adapted to Lean 4 using the Lean4 Game Engine.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- Image "" -- TODO: Not implemented
/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
