
import java.io.File;

import unbbayes.controller.exception.InvalidOperationException;
import unbbayes.controller.mebn.MEBNFactory;
import unbbayes.controller.mebn.MEBNFactoryImpl;
import unbbayes.io.exception.UBIOException;
import unbbayes.prs.mebn.MFrag;
import unbbayes.prs.mebn.MultiEntityBayesianNetwork;
import unbbayes.prs.mebn.RandomVariableFinding;
import unbbayes.prs.mebn.ResidentNode;
import unbbayes.prs.mebn.entity.Entity;
import unbbayes.prs.mebn.entity.ObjectEntity;
import unbbayes.prs.mebn.entity.ObjectEntityInstance;
import unbbayes.prs.mebn.entity.ObjectEntityInstanceOrdereable;
import unbbayes.prs.mebn.entity.exception.EntityInstanceAlreadyExistsException;
import unbbayes.prs.mebn.entity.exception.TypeException;
import unbbayes.prs.mebn.exception.DuplicatedNameException;
import unbbayes.prs.mebn.exception.MEBNException;
import unbbayes.prs.mebn.exception.ReservedWordException;
import unbbayes.prs.mebn.kb.KnowledgeBase;
import unbbayes.prs.mebn.kb.powerloom.PowerLoomKB;


public class MebnUtil {
	
	private KnowledgeBase knowledgeBase;
	private MEBNFactory mebnFactory; 
	private MultiEntityBayesianNetwork multiEntityBayesianNetwork;
	
	public MebnUtil(MultiEntityBayesianNetwork mebn) {
		this.multiEntityBayesianNetwork = mebn;
		this.mebnFactory = new MEBNFactoryImpl(); 
	}

	private void checkName(String name) throws DuplicatedNameException,
			ReservedWordException {
		if (multiEntityBayesianNetwork.getNamesUsed().contains(name)) {
			throw new DuplicatedNameException(name);
		}
		if (mebnFactory.getReservedWords().contains(name)) {
			throw new ReservedWordException(name);
		}
	}

	/*-------------------------------------------------------------------------*/
	/* Object Entities Instances */
	/*-------------------------------------------------------------------------*/

	/**
	 * Create a new Object Entity Instance of the Object Entity.
	 * 
	 * @param entity
	 * @param nameInstance
	 * @throws EntityInstanceAlreadyExistsException
	 * @throws InvalidOperationException
	 * @throws DuplicatedNameException
	 * @throws ReservedWordException
	 */
	public void createEntityIntance(ObjectEntity entity, String nameInstance)
			throws EntityInstanceAlreadyExistsException,
			InvalidOperationException, DuplicatedNameException,
			ReservedWordException {

		if (entity.isOrdereable()) {
			throw new InvalidOperationException();
		}

		checkName(nameInstance);

		if (multiEntityBayesianNetwork.getObjectEntityContainer()
				.getEntityInstanceByName(nameInstance) != null) {
//			throw new EntityInstanceAlreadyExistsException();
		} else {
			try {
				ObjectEntityInstance instance = entity
						.addInstance(nameInstance);
				multiEntityBayesianNetwork.getObjectEntityContainer()
						.addEntityInstance(instance);
				multiEntityBayesianNetwork.getNamesUsed().add(nameInstance);
			} catch (TypeException e1) {
				e1.printStackTrace();
			} catch (EntityInstanceAlreadyExistsException e) {
				e.printStackTrace();
			}
		}
	}

	public void createEntityIntanceOrdereable(ObjectEntity entity,
			String nameInstance, ObjectEntityInstanceOrdereable previous)
			throws EntityInstanceAlreadyExistsException,
			InvalidOperationException, DuplicatedNameException,
			ReservedWordException {

		if (!entity.isOrdereable()) {
			throw new InvalidOperationException();
		}

		checkName(nameInstance);

		if (multiEntityBayesianNetwork.getObjectEntityContainer()
				.getEntityInstanceByName(nameInstance) != null) {
			throw new EntityInstanceAlreadyExistsException();
		} else {
			try {
				ObjectEntityInstanceOrdereable instance = (ObjectEntityInstanceOrdereable) entity
						.addInstance(nameInstance);

				instance.setPrev(previous);
				if (previous != null) {
					previous.setProc(instance);
				}

				multiEntityBayesianNetwork.getObjectEntityContainer()
						.addEntityInstance(instance);
				multiEntityBayesianNetwork.getNamesUsed().add(nameInstance);
			} catch (TypeException e1) {
				e1.printStackTrace();
			} catch (EntityInstanceAlreadyExistsException e) {
				e.printStackTrace();
			}
		}
	}

	public void renameEntityIntance(ObjectEntityInstance entity, String newName)
			throws EntityInstanceAlreadyExistsException,
			DuplicatedNameException, ReservedWordException {

		checkName(newName);

		if (multiEntityBayesianNetwork.getObjectEntityContainer()
				.getEntityInstanceByName(newName) != null) {
			throw new EntityInstanceAlreadyExistsException();
		} else {
			multiEntityBayesianNetwork.getNamesUsed().remove(entity.getName());
			entity.setName(newName);
			multiEntityBayesianNetwork.getNamesUsed().add(newName);

		}
	}
	
	public void removeAllEntityInstances() {
		for (ObjectEntity entity : multiEntityBayesianNetwork.getObjectEntityContainer().getListEntity()) {
			for (ObjectEntityInstance entityInstance : multiEntityBayesianNetwork.getObjectEntityContainer().getListEntityInstances()) {
				multiEntityBayesianNetwork.getNamesUsed().remove(entityInstance.getName());
			}
			multiEntityBayesianNetwork.getObjectEntityContainer().clearAllInstances(entity);
		}
	}

	public void removeEntityInstance(ObjectEntityInstance entity) {
		multiEntityBayesianNetwork.getObjectEntityContainer()
				.removeEntityInstance(entity);
		multiEntityBayesianNetwork.getNamesUsed().remove(entity.getName());
	}

	public void removeEntityInstanceOrdereable(
			ObjectEntityInstanceOrdereable entity) {
		ObjectEntityInstanceOrdereable
				.removeEntityInstanceOrdereableReferences(entity);
		multiEntityBayesianNetwork.getObjectEntityContainer()
				.removeEntityInstance(entity);
		multiEntityBayesianNetwork.getNamesUsed().remove(entity.getName());
	}

	public void upEntityInstance(ObjectEntityInstanceOrdereable entity) {
		ObjectEntityInstanceOrdereable.upEntityInstance(entity);
	}

	public void downEntityInstance(ObjectEntityInstanceOrdereable entity) {
		ObjectEntityInstanceOrdereable.downEntityInstance(entity);
	}

	/*-------------------------------------------------------------------------*/
	/* Findings */
	/*-------------------------------------------------------------------------*/

	public void createRandomVariableFinding(ResidentNode residentNode,
			ObjectEntityInstance[] arguments, Entity state) {

		RandomVariableFinding finding = new RandomVariableFinding(residentNode,
				arguments, state, this.multiEntityBayesianNetwork);

		residentNode.addRandomVariableFinding(finding);
	}

	/*-------------------------------------------------------------------------*/
	/* Knowledge Base */
	/*-------------------------------------------------------------------------*/

	public KnowledgeBase getKnowledgeBase() {
		if (knowledgeBase == null) {
			knowledgeBase = PowerLoomKB.getNewInstanceKB();
		}
		return knowledgeBase;
	}
	/**
	 * Insert the MEBN Generative into KB. (Object Entities and Domain Resident
	 * Nodes)
	 */
	private void loadGenerativeMEBNIntoKB() {

		KnowledgeBase knowledgeBase = getKnowledgeBase();

		for (ObjectEntity entity : multiEntityBayesianNetwork.getObjectEntityContainer().getListEntity()) {
			knowledgeBase.createEntityDefinition(entity);
		}

		for (MFrag mfrag : multiEntityBayesianNetwork.getDomainMFragList()) {
			for (ResidentNode resident : mfrag.getResidentNodeList()) {
				knowledgeBase.createRandomVariableDefinition(resident);
			}
		}
	}

	/**
	 * Insert the findings into KB.
	 */
	private void loadFindingsIntoKB() {

		KnowledgeBase knowledgeBase = getKnowledgeBase();

		
		
		
		
		for (ObjectEntityInstance instance : multiEntityBayesianNetwork.getObjectEntityContainer().getListEntityInstances()) {
			knowledgeBase.insertEntityInstance(instance);
		}

		for (MFrag mfrag : multiEntityBayesianNetwork.getDomainMFragList()) {
			for (ResidentNode residentNode : mfrag.getResidentNodeList()) {
				for (RandomVariableFinding finding : residentNode.getRandomVariableFindingList()) {
					knowledgeBase.insertRandomVariableFinding(finding);
					
				}
			}
		}
	}

	public void removeAllFindings() {

		for (MFrag mfrag : multiEntityBayesianNetwork.getDomainMFragList()) {
			for (ResidentNode residentNode : mfrag.getResidentNodeList()) {
				residentNode.cleanRandomVariableFindingList();
			}
		}

	}

	public void clearKnowledgeBase() {
		getKnowledgeBase().clearKnowledgeBase();
	}

	public void saveGenerativeMTheory(File file) {
		getKnowledgeBase().saveGenerativeMTheory(
				multiEntityBayesianNetwork, file);
	}

	public void saveFindingsFile(File file) {

		createKnowledgeBase();
		getKnowledgeBase().saveFindings(multiEntityBayesianNetwork, file);

	}

	public void loadFindingsFile(File file) throws UBIOException, MEBNException {

		Exception lastException = null;

		// init the powerloom knowledge base
		createKnowledgeBase();
		getKnowledgeBase().loadModule(file, true);

		// init gui
		for (ResidentNode resident : this.multiEntityBayesianNetwork.getDomainResidentNodes()) {
			try {
				this.knowledgeBase.fillFindings(resident);
				
			} catch (Exception e) {
				e.printStackTrace();
				lastException = e;
				continue;
			}
		}

		if (lastException != null) {
			// commenting below... PowerLoom was throwing stack trace as
			// message...
			// throw new MEBNException(lastException);
			throw new MEBNException("Loading findings error!");
		}
	}

	private void createKnowledgeBase() {
		// Must remove unwanted findings entered previously
		getKnowledgeBase().clearKnowledgeBase();
		loadGenerativeMEBNIntoKB();
		loadFindingsIntoKB();
		// baseCreated = true;
	}
	
}